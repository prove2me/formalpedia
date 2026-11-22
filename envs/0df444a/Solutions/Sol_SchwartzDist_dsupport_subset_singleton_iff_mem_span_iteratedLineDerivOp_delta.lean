-- Prove2me | solution 1 for SchwartzDist.dsupport_subset_singleton_iff_mem_span_iteratedLineDerivOp_delta
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:59:27.635798+00:00
-- url     : https://prove2.me/submissions/77842660-0965-447f-b1fc-3012ca2b552c

import Mathlib
import Theorems.Thm_SchwartzDist_temperedDistribution_ext_of_hasCompactSupport

open SchwartzMap LineDeriv Topology Filter

set_option autoImplicit false

open scoped ContDiff Manifold

namespace Sol_SchwartzDist_dsupport_subset_singleton_iff_mem_span_iteratedLineDerivOp_delta

open Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Algebraic part -/




/-- Evaluation of an iterated derivative of a tempered distribution. -/
lemma iteratedLineDerivOp_apply_eq (n : ℕ) (m : Fin n → E) (S : 𝓢'(E, ℂ)) (φ : 𝓢(E, ℂ)) :
    (∂^{m} S) φ = (-1 : ℂ) ^ n * S (∂^{m ∘ Fin.rev} φ) := by
  induction n generalizing S φ with
  | zero => simp
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left, TemperedDistribution.lineDerivOp_apply_apply, ih,
      iteratedLineDerivOp_neg, map_neg, iteratedLineDerivOp_succ_right (m ∘ Fin.rev)]
    have h1 : Fin.init (m ∘ Fin.rev) = Fin.tail m ∘ Fin.rev := by
      funext i
      simp [Fin.init, Fin.tail, Fin.rev_castSucc]
    have h2 : (m ∘ Fin.rev) (Fin.last n) = m 0 := by simp
    rw [h1, h2, pow_succ]
    ring

/-- The converse direction. -/
lemma isVanishingOn_of_mem_span (x₀ : E) (T : 𝓢'(E, ℂ))
    (hT : T ∈ Submodule.span ℂ (Set.range fun p : (Σ k : ℕ, Fin k → E) =>
        ∂^{p.2} (TemperedDistribution.delta x₀))) :
    IsVanishingOn (⇑T) {x₀}ᶜ := by
  induction hT using Submodule.span_induction with
  | mem S hS =>
    obtain ⟨p, rfl⟩ := hS
    exact Distribution.TemperedDistribution.IsVanishingOn.iteratedLineDerivOp
      (TemperedDistribution.isVanishingOn_delta x₀) p.2
  | zero => intro u _; rfl
  | add S S' _ _ h h' => intro u hu; simp [h u hu, h' u hu]
  | smul c S _ h => intro u hu; simp [h u hu]


/-- Linear algebra: a distribution vanishing on all functions flat to order `N` at `x₀`
is a combination of derivatives of `δ_{x₀}`. -/
lemma mem_span_of_vanish (x₀ : E) (T : 𝓢'(E, ℂ)) (N : ℕ)
    (hN : ∀ φ : 𝓢(E, ℂ), (∀ j ≤ N, iteratedFDeriv ℝ j (φ : E → ℂ) x₀ = 0) → T φ = 0) :
    T ∈ Submodule.span ℂ (Set.range fun p : (Σ k : ℕ, Fin k → E) =>
        ∂^{p.2} (TemperedDistribution.delta x₀)) := by
  classical
  set d := Module.finrank ℝ E
  let b : Module.Basis (Fin d) ℝ E := Module.finBasis ℝ E
  let L' : (Σ j : Fin (N + 1), (Fin j → Fin d)) → 𝓢'(E, ℂ) :=
    fun p => ∂^{b ∘ p.2} (TemperedDistribution.delta x₀)
  let Φ : 𝓢'(E, ℂ) →ₗ[ℂ] (𝓢(E, ℂ) →ₗ[ℂ] ℂ) :=
    { toFun := fun S => (S : 𝓢(E, ℂ) →L[ℂ] ℂ).toLinearMap
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΦ : Function.Injective Φ := by
    intro S S' h
    exact ContinuousLinearMap.ext fun φ => LinearMap.congr_fun h φ
  have hker : ⨅ i, LinearMap.ker (Φ (L' i)) ≤ LinearMap.ker (Φ T) := by
    intro φ hφ
    rw [Submodule.mem_iInf] at hφ
    rw [LinearMap.mem_ker]
    apply hN φ
    intro j hj
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    apply Module.Basis.ext_multilinear (fun _ => b)
    intro τ
    have h := hφ ⟨⟨j, Nat.lt_succ_of_le hj⟩, τ ∘ Fin.rev⟩
    rw [LinearMap.mem_ker] at h
    change (∂^{b ∘ (τ ∘ Fin.rev)} (TemperedDistribution.delta x₀)) φ = 0 at h
    rw [iteratedLineDerivOp_apply_eq, TemperedDistribution.delta_apply,
      SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv] at h
    have h' : iteratedFDeriv ℝ j (φ : E → ℂ) x₀ (fun i => b (τ i)) = 0 := by
      have hne : ((-1 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
      have h3 := (mul_eq_zero.mp h).resolve_left hne
      convert h3 using 2
      funext i
      simp
    simpa using h'
  have hmem := mem_span_of_iInf_ker_le_ker hker
  have hrange : Set.range (fun i => Φ (L' i)) = Φ '' Set.range L' := by
    rw [← Set.range_comp]; rfl
  rw [hrange, Submodule.span_image, Submodule.mem_map] at hmem
  obtain ⟨S, hS, hST⟩ := hmem
  rw [← hΦ hST]
  refine Submodule.span_mono ?_ hS
  rintro _ ⟨p, rfl⟩
  exact ⟨⟨p.1, b ∘ p.2⟩, rfl⟩


/-! ### Localization -/




/-- Localization, compactly supported case: a tempered distribution supported in `{x₀}`
vanishes on compactly supported test functions whose support avoids `x₀`. -/
lemma vanish_compact (x₀ : E) (T : 𝓢'(E, ℂ)) (hT : dsupport (⇑T) ⊆ {x₀})
    (u : 𝓢(E, ℂ)) (hu : HasCompactSupport (u : E → ℂ)) (hx : x₀ ∉ tsupport (u : E → ℂ)) :
    T u = 0 := by
  classical
  set K := tsupport (u : E → ℂ) with hKdef
  have hK : IsCompact K := hu
  have hloc : ∀ y ∈ K, ∃ s : Set E, IsVanishingOn (⇑T) s ∧ IsOpen s ∧ y ∈ s := by
    intro y hy
    have hy' : y ∉ dsupport (⇑T) := by
      intro h
      have := hT h
      rw [Set.mem_singleton_iff] at this
      exact hx (this ▸ hy)
    exact (notMem_dsupport_iff y).mp hy'
  choose! U hUv hUo hUy using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : K => U y) (fun y => hUo y y.2)
    (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hUy y hy⟩)
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) (isClosed_tsupport (u : E → ℂ))
    (fun i : t => U ((i : K) : E)) (fun i => hUo _ (i : K).2) (by
      intro y hy
      have := ht hy
      simp only [Set.mem_iUnion] at this ⊢
      obtain ⟨i, hi, hyi⟩ := this
      exact ⟨⟨i, hi⟩, hyi⟩)
  have hsm : ∀ i : t, ContDiff ℝ ∞ (fun x => ρ i x • u x) := fun i =>
    (contMDiff_iff_contDiff.mp (ρ i).contMDiff).smul (u.smooth ⊤)
  have hcs : ∀ i : t, HasCompactSupport (fun x => ρ i x • u x) := fun i =>
    hu.mono (Function.support_smul_subset_right (fun x => ρ i x) (u : E → ℂ))
  let v : t → 𝓢(E, ℂ) := fun i => (hcs i).toSchwartzMap (hsm i)
  have hv : ∀ i, T (v i) = 0 := by
    intro i
    apply hUv _ (i : K).2
    calc tsupport (v i : E → ℂ) = tsupport (fun x => ρ i x • u x) := rfl
      _ ⊆ tsupport (ρ i) := tsupport_smul_subset_left _ _
      _ ⊆ U ((i : K) : E) := hρ i
  have hsum : u = ∑ i, v i := by
    ext x
    rw [sum_apply]
    change u x = ∑ i, ρ i x • u x
    rw [← Finset.sum_smul]
    by_cases hxK : x ∈ K
    · have h1 := ρ.sum_eq_one hxK
      rw [finsum_eq_sum_of_fintype] at h1
      rw [h1, one_smul]
    · have h0 : u x = 0 := image_eq_zero_of_notMem_tsupport hxK
      rw [h0, smul_zero]
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ => hv i

/-- Localization: a tempered distribution supported in `{x₀}` vanishes on every Schwartz
function whose support avoids `x₀`. -/
lemma vanish (x₀ : E) (T : 𝓢'(E, ℂ)) (hT : dsupport (⇑T) ⊆ {x₀})
    (u : 𝓢(E, ℂ)) (hx : x₀ ∉ tsupport (u : E → ℂ)) : T u = 0 := by
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp (isClosed_tsupport (u : E → ℂ)).isOpen_compl x₀ hx
  let χ : ContDiffBump x₀ := ⟨r / 2, r, by positivity, by linarith⟩
  let g : E → ℂ := fun x => ((χ x : ℝ) : ℂ)
  have hgc : HasCompactSupport g := χ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hgs : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hg : g.HasTemperateGrowth := hgc.hasTemperateGrowth hgs
  let S : 𝓢'(E, ℂ) := T - TemperedDistribution.smulLeftCLM ℂ g T
  have hS : S = 0 := by
    apply SchwartzDist.temperedDistribution_ext_of_hasCompactSupport
    intro φ hφ
    have h1 : S φ = T (φ - SchwartzMap.smulLeftCLM ℂ g φ) := by
      simp [S, map_sub]
    rw [h1]
    have hcoe : ((φ - SchwartzMap.smulLeftCLM ℂ g φ : 𝓢(E, ℂ)) : E → ℂ) =
        fun x => φ x - g x • φ x := by
      ext y
      simp [SchwartzMap.smulLeftCLM_apply_apply hg]
    apply vanish_compact x₀ T hT
    · rw [hcoe]
      refine hφ.mono (Function.support_subset_iff'.mpr fun x hx => ?_)
      rw [Function.notMem_support] at hx
      simp [hx]
    · rw [hcoe, notMem_tsupport_iff_eventuallyEq]
      filter_upwards [Metric.ball_mem_nhds x₀ (by positivity : (0 : ℝ) < r / 2)] with y hy
      have h1 : χ y = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
      simp [g, h1]
  have h2 : SchwartzMap.smulLeftCLM ℂ g u = 0 := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply hg]
    by_cases hy : y ∈ Metric.ball x₀ r
    · have : u y = 0 := image_eq_zero_of_notMem_tsupport (hball hy)
      simp [this]
    · have : χ y = 0 := χ.zero_of_le_dist (by
        rw [Metric.mem_ball, not_lt] at hy
        exact hy)
      simp [g, this]
  have h3 : S u = 0 := by rw [hS]; rfl
  simpa [S, h2] using h3


/-! ### Cut-off estimates and finite order -/



/-- Taylor-type bound: if the derivatives of order `≤ N` of `φ` vanish at `x₀`, then
`‖D^{N+1-m} φ(x)‖ ≤ B ρ^m` on the ball of radius `ρ` about `x₀`. -/
lemma taylor_bound (φ : 𝓢(E, ℂ)) (x₀ : E) (N : ℕ)
    (hφ : ∀ j ≤ N, iteratedFDeriv ℝ j (φ : E → ℂ) x₀ = 0) :
    ∀ m ≤ N + 1, ∀ ρ : ℝ, 0 ≤ ρ → ∀ x ∈ Metric.closedBall x₀ ρ,
      ‖iteratedFDeriv ℝ (N + 1 - m) (φ : E → ℂ) x‖ ≤
        SchwartzMap.seminorm ℂ 0 (N + 1) φ * ρ ^ m := by
  intro m
  induction m with
  | zero =>
    intro _ ρ _ x _
    simpa using φ.norm_iteratedFDeriv_le_seminorm ℂ (N + 1) x
  | succ m ih =>
    intro hm ρ hρ x hx
    have hj : N + 1 - (m + 1) + 1 = N + 1 - m := by omega
    have hjN : N + 1 - (m + 1) ≤ N := by omega
    have hdiff : ∀ y ∈ Metric.closedBall x₀ ρ,
        DifferentiableAt ℝ (iteratedFDeriv ℝ (N + 1 - (m + 1)) (φ : E → ℂ)) y :=
      fun y _ => ((φ.smooth ⊤).differentiable_iteratedFDeriv
        (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (N + 1 - (m + 1))))) y
    have hbound : ∀ y ∈ Metric.closedBall x₀ ρ,
        ‖fderiv ℝ (iteratedFDeriv ℝ (N + 1 - (m + 1)) (φ : E → ℂ)) y‖ ≤
          SchwartzMap.seminorm ℂ 0 (N + 1) φ * ρ ^ m := by
      intro y hy
      rw [norm_fderiv_iteratedFDeriv, hj]
      exact ih (by omega) ρ hρ y hy
    have h := (convex_closedBall x₀ ρ).norm_image_sub_le_of_norm_fderiv_le hdiff hbound
      (Metric.mem_closedBall_self hρ) hx
    rw [hφ _ hjN, sub_zero] at h
    have hxr : ‖x - x₀‖ ≤ ρ := mem_closedBall_iff_norm.mp hx
    calc _ ≤ SchwartzMap.seminorm ℂ 0 (N + 1) φ * ρ ^ m * ‖x - x₀‖ := h
      _ ≤ SchwartzMap.seminorm ℂ 0 (N + 1) φ * ρ ^ m * ρ := by gcongr
      _ = _ := by ring

/-- A fixed bump: `1` on `closedBall 0 (1/2)`, supported in `ball 0 1`. -/
noncomputable def chi (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : ContDiffBump (0 : E) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The bump as a Schwartz function. -/
noncomputable def chiS (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : 𝓢(E, ℝ) :=
  (chi E).hasCompactSupport.toSchwartzMap (chi E).contDiff

/-- The rescaled cut-off around `x₀`. -/
noncomputable def cutf (x₀ : E) (ε : ℝ) : E → ℝ := fun x => chi E (ε⁻¹ • (x - x₀))

lemma cutf_contDiff (x₀ : E) (ε : ℝ) : ContDiff ℝ ∞ (cutf x₀ ε) :=
  (chi E).contDiff.comp ((contDiff_id.sub contDiff_const).const_smul ε⁻¹)

lemma norm_iteratedFDeriv_cutf_le (x₀ : E) (ε : ℝ) (hε : 0 < ε) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (cutf x₀ ε) x‖ ≤ ε⁻¹ ^ i * SchwartzMap.seminorm ℝ 0 i (chiS E) := by
  have h1 : iteratedFDeriv ℝ i (cutf x₀ ε) x =
      iteratedFDeriv ℝ i (fun z : E => chi E (ε⁻¹ • z)) (x - x₀) :=
    iteratedFDeriv_comp_sub (f := fun z : E => chi E (ε⁻¹ • z)) i x₀ x
  rw [h1, iteratedFDeriv_comp_const_smul ε⁻¹ (chi E).contDiff]
  simp only
  rw [norm_smul, norm_pow, norm_inv, Real.norm_of_nonneg hε.le]
  gcongr
  exact (chiS E).norm_iteratedFDeriv_le_seminorm ℝ i _

lemma cutf_eq_one (x₀ : E) (ε : ℝ) (hε : 0 < ε) (y : E) (hy : y ∈ Metric.ball x₀ (ε / 2)) :
    cutf x₀ ε y = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hε.le]
  rw [Metric.mem_ball, dist_eq_norm] at hy
  show ε⁻¹ * ‖y - x₀‖ ≤ 1 / 2
  rw [inv_mul_le_iff₀ hε]
  linarith

lemma cutf_eq_zero (x₀ : E) (ε : ℝ) (hε : 0 < ε) (y : E) (hy : ε ≤ ‖y - x₀‖) :
    cutf x₀ ε y = 0 := by
  apply ContDiffBump.zero_of_le_dist
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hε.le]
  show 1 ≤ ε⁻¹ * ‖y - x₀‖
  rw [le_inv_mul_iff₀ hε, mul_one]
  exact hy

lemma pow_aux (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (i n N : ℕ) (hi : i ≤ n) (hn : n ≤ N) :
    ε⁻¹ ^ i * ε ^ (N + 1 - (n - i)) ≤ ε := by
  have h1 : N + 1 - (n - i) = i + (N + 1 - n) := by omega
  rw [h1, pow_add, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hε.ne'), one_mul]
  calc ε ^ (N + 1 - n) ≤ ε ^ 1 := pow_le_pow_of_le_one hε.le hε1 (by omega)
    _ = ε := pow_one ε

/-- The key estimate: the `(k, n)` Schwartz quantity of the cut-off `χ_ε φ` is `O(ε)` when
`n ≤ N` and `φ` is flat to order `N` at `x₀`. -/
lemma cut_bound (φ : 𝓢(E, ℂ)) (x₀ : E) (N : ℕ)
    (hφ : ∀ j ≤ N, iteratedFDeriv ℝ j (φ : E → ℂ) x₀ = 0) (k n : ℕ) (hn : n ≤ N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => cutf x₀ ε y • φ y) x‖ ≤ M * ε := by
  set B := SchwartzMap.seminorm ℂ 0 (N + 1) φ
  refine ⟨(‖x₀‖ + 1) ^ k * ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i (chiS E) * B, by positivity, ?_⟩
  intro ε hε hε1 x
  by_cases hx : x ∈ Metric.closedBall x₀ ε
  · have hxn : ‖x‖ ≤ ‖x₀‖ + 1 := by
      have : ‖x - x₀‖ ≤ ε := mem_closedBall_iff_norm.mp hx
      calc ‖x‖ = ‖x₀ + (x - x₀)‖ := by rw [add_sub_cancel]
        _ ≤ ‖x₀‖ + ‖x - x₀‖ := norm_add_le _ _
        _ ≤ ‖x₀‖ + 1 := by linarith
    have hf : ContDiff ℝ n (cutf x₀ ε) := (cutf_contDiff x₀ ε).of_le (mod_cast le_top)
    have hg : ContDiff ℝ n (φ : E → ℂ) := (φ.smooth ⊤).of_le (mod_cast le_top)
    have hL := norm_iteratedFDeriv_smul_le hf hg x (n := n) le_rfl
    have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (cutf x₀ ε) x‖ * ‖iteratedFDeriv ℝ (n - i) (φ : E → ℂ) x‖ ≤
        (∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i (chiS E) * B) * ε := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hT := taylor_bound φ x₀ N hφ (N + 1 - (n - i)) (by omega) ε hε.le x hx
      rw [show N + 1 - (N + 1 - (n - i)) = n - i by omega] at hT
      have hC := norm_iteratedFDeriv_cutf_le x₀ ε hε i x
      have hP := pow_aux ε hε hε1 i n N hi' hn
      have hS0 : 0 ≤ SchwartzMap.seminorm ℝ 0 i (chiS E) := apply_nonneg _ _
      have hB0 : 0 ≤ B := apply_nonneg _ _
      calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutf x₀ ε) x‖ *
            ‖iteratedFDeriv ℝ (n - i) (φ : E → ℂ) x‖
          ≤ (n.choose i : ℝ) * (ε⁻¹ ^ i * SchwartzMap.seminorm ℝ 0 i (chiS E)) *
            (B * ε ^ (N + 1 - (n - i))) := by gcongr
        _ = (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i (chiS E) * B *
            (ε⁻¹ ^ i * ε ^ (N + 1 - (n - i))) := by ring
        _ ≤ (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i (chiS E) * B * ε := by gcongr
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => cutf x₀ ε y • φ y) x‖
        ≤ (‖x₀‖ + 1) ^ k * ((∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i (chiS E) * B) * ε) := by
          gcongr
          exact hL.trans hsum
      _ = _ := by ring
  · have hx' : ε < ‖x - x₀‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hx
      exact hx
    have hev : (fun y => cutf x₀ ε y • φ y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      have hopen : IsOpen {y : E | ε < ‖y - x₀‖} :=
        isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
      filter_upwards [hopen.mem_nhds hx'] with y hy
      rw [cutf_eq_zero x₀ ε hε y (le_of_lt hy), zero_smul]
    rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    have : 0 ≤ (‖x₀‖ + 1) ^ k * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i (chiS E) * B := by positivity
    positivity

/-- Finite order + cut-off: a tempered distribution vanishing on Schwartz functions supported
away from `x₀` vanishes on all Schwartz functions flat to some finite order `N` at `x₀`. -/
lemma exists_order (x₀ : E) (T : 𝓢'(E, ℂ))
    (hvan : ∀ u : 𝓢(E, ℂ), x₀ ∉ tsupport (u : E → ℂ) → T u = 0) :
    ∃ N : ℕ, ∀ φ : 𝓢(E, ℂ), (∀ j ≤ N, iteratedFDeriv ℝ j (φ : E → ℂ) x₀ = 0) → T φ = 0 := by
  obtain ⟨s, C, -, hq⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ)
    ((normSeminorm ℂ ℂ).comp (T : 𝓢(E, ℂ) →L[ℂ] ℂ).toLinearMap)
    (continuous_norm.comp (T : 𝓢(E, ℂ) →L[ℂ] ℂ).continuous)
  refine ⟨s.sup Prod.snd, fun φ hφ => ?_⟩
  set N := s.sup Prod.snd
  have hM : ∀ p ∈ s, ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : E,
      ‖x‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (fun y => cutf x₀ ε y • φ y) x‖ ≤ M * ε :=
    fun p hp => cut_bound φ x₀ N hφ p.1 p.2 (Finset.le_sup (f := Prod.snd) hp)
  choose! M hM0 hMb using hM
  set Mt := ∑ p ∈ s, M p
  have hMt0 : 0 ≤ Mt := Finset.sum_nonneg hM0
  have hcut : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ‖T φ‖ ≤ (C : ℝ) * (Mt * ε) := by
    intro ε hε hε1
    have hcs : HasCompactSupport (fun y => cutf x₀ ε y • φ y) := by
      have h0 : HasCompactSupport (cutf x₀ ε) := by
        have : HasCompactSupport (fun x : E => chi E x) := (chi E).hasCompactSupport
        have h2 := this.comp_homeomorph ((Homeomorph.subRight x₀).trans
          (Homeomorph.smulOfNeZero ε⁻¹ (inv_ne_zero hε.ne')))
        exact h2
      exact h0.smul_right
    have hsm : ContDiff ℝ ∞ (fun y => cutf x₀ ε y • φ y) :=
      (cutf_contDiff x₀ ε).smul (φ.smooth ⊤)
    let ψ : 𝓢(E, ℂ) := hcs.toSchwartzMap hsm
    have hTψ : T φ = T ψ := by
      have h0 : T (φ - ψ) = 0 := by
        apply hvan
        rw [notMem_tsupport_iff_eventuallyEq]
        filter_upwards [Metric.ball_mem_nhds x₀ (half_pos hε)] with y hy
        change φ y - cutf x₀ ε y • φ y = 0
        rw [cutf_eq_one x₀ ε hε y hy, one_smul, sub_self]
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    rw [hTψ]
    have h1 : ‖T ψ‖ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ E ℂ)) ψ := by
      have := hq ψ
      simp only [Seminorm.comp_apply, coe_normSeminorm, smul_apply] at this
      rw [NNReal.smul_def, smul_eq_mul] at this
      exact this
    have h2 : (s.sup (schwartzSeminormFamily ℂ E ℂ)) ψ ≤ Mt * ε := by
      apply Seminorm.finset_sup_apply_le (by positivity)
      intro p hp
      apply SchwartzMap.seminorm_le_bound ℂ p.1 p.2 ψ (by positivity)
      intro x
      calc _ ≤ M p * ε := hMb p hp ε hε hε1 x
        _ ≤ Mt * ε := by
          gcongr
          exact Finset.single_le_sum (fun p hp => hM0 p hp) hp
    calc ‖T ψ‖ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ E ℂ)) ψ := h1
      _ ≤ (C : ℝ) * (Mt * ε) := by gcongr
  have hlim : Tendsto (fun n : ℕ => (C : ℝ) * (Mt * (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat).const_mul Mt).const_mul (C : ℝ)
  have hle : ‖T φ‖ ≤ 0 := by
    refine ge_of_tendsto' hlim fun n => hcut _ (by positivity) ?_
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  exact norm_le_zero_iff.mp hle

end Sol_SchwartzDist_dsupport_subset_singleton_iff_mem_span_iteratedLineDerivOp_delta

open Sol_SchwartzDist_dsupport_subset_singleton_iff_mem_span_iteratedLineDerivOp_delta in
theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (x₀ : E) (T : 𝓢'(E, ℂ)) :
    Distribution.dsupport (⇑T) ⊆ {x₀} ↔
      T ∈ Submodule.span ℂ (Set.range fun p : (Σ k : ℕ, Fin k → E) =>
        ∂^{p.2} (TemperedDistribution.delta x₀)) := by
  constructor
  · intro hT
    obtain ⟨N, hN⟩ := exists_order x₀ T (fun u hu => vanish x₀ T hT u hu)
    exact mem_span_of_vanish x₀ T N hN
  · intro hT y hy
    rw [Distribution.mem_dsupport_iff] at hy
    exact hy {x₀} (isVanishingOn_of_mem_span x₀ T hT) isClosed_singleton
