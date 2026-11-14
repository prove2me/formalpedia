-- Prove2me | solution 1 for TeschlQM.Weyl.weyl
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T11:02:35.425287+00:00
-- url     : https://prove2.me/submissions/14f1b95f-7dea-432e-897a-b8e8bef9378e

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum

set_option autoImplicit false

open scoped InnerProductSpace LinearPMap

namespace WeylP

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


/-- A self-adjoint operator is symmetric. -/
theorem symm_of_selfAdjoint (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) :
    ∀ x y : A.domain, ⟪A x, (y : H)⟫_ℂ = ⟪(x : H), A y⟫_ℂ := by
  have hA' : A† = A := hA
  have hle : A ≤ A† := by rw [hA']
  intro x y
  have hx : (x : H) ∈ A†.domain := hle.1 x.2
  have h1 : A x = A† ⟨x, hx⟩ := hle.2 (x := x) (y := ⟨x, hx⟩) rfl
  rw [h1]
  exact LinearPMap.adjoint_isFormalAdjoint hA.dense_domain ⟨x, hx⟩ y


/-- P6a: the resolvent identity `R_a - R_b = (a - b) R_a R_b`. -/
theorem resolvent_identity (X : H →ₗ.[ℂ] H) (a b : ℂ) (Ra Rb : H →L[ℂ] H)
    (ha : TeschlQM.Shared.IsResolventAt X a Ra) (hb : TeschlQM.Shared.IsResolventAt X b Rb)
    (φ : H) : Ra φ - Rb φ = (a - b) • Ra (Rb φ) := by
  obtain ⟨hD, hX⟩ := hb.1 φ
  have e := ha.2 ⟨Rb φ, hD⟩
  have h1 : X ⟨Rb φ, hD⟩ - a • Rb φ = φ - (a - b) • Rb φ := by
    calc X ⟨Rb φ, hD⟩ - a • Rb φ = (X ⟨Rb φ, hD⟩ - b • Rb φ) - (a - b) • Rb φ := by
          rw [sub_smul]; abel
      _ = φ - (a - b) • Rb φ := by rw [hX]
  simp only at e
  rw [h1, map_sub, map_smul] at e
  calc Ra φ - Rb φ = Ra φ - (Ra φ - (a - b) • Ra (Rb φ)) := by rw [e]
    _ = (a - b) • Ra (Rb φ) := by abel


/-- P8a: if `a ≠ b` are both in `ρ(X)` then `(b - a)⁻¹ - R_X(a)` is invertible. -/
theorem isUnit_of_resolvent (X : H →ₗ.[ℂ] H) (a b : ℂ) (hab : a ≠ b) (Ra Rb : H →L[ℂ] H)
    (ha : TeschlQM.Shared.IsResolventAt X a Ra) (hb : TeschlQM.Shared.IsResolventAt X b Rb) :
    IsUnit (algebraMap ℂ (H →L[ℂ] H) ((b - a)⁻¹) - Ra) := by
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  set c : ℂ := (b - a)⁻¹ with hc
  have hcb : c * (b - a) = 1 := inv_mul_cancel₀ hba
  have hbc : (b - a) * c = 1 := mul_inv_cancel₀ hba
  have k1 : ∀ φ, (b - a) • Ra (Rb φ) = Rb φ - Ra φ := by
    intro φ
    have e := resolvent_identity X a b Ra Rb ha hb φ
    rw [show b - a = -(a - b) by ring, neg_smul, ← e]; abel
  have k2 : ∀ φ, (b - a) • Rb (Ra φ) = Rb φ - Ra φ := fun φ =>
    (resolvent_identity X b a Rb Ra hb ha φ).symm
  have hal : ∀ φ, algebraMap ℂ (H →L[ℂ] H) c φ = c • φ := by
    intro φ; simp [Algebra.algebraMap_eq_smul_one]
  refine ⟨⟨algebraMap ℂ (H →L[ℂ] H) c - Ra, (b - a) • (1 + (b - a) • Rb), ?_, ?_⟩, rfl⟩
  · ext φ
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply, hal]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply]
    rw [smul_smul c, hcb, one_smul, map_smul, map_add, map_smul, k1]
    have h3 : Ra φ + (Rb φ - Ra φ) = Rb φ := by abel
    rw [h3]; abel
  · ext φ
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply, hal]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply]
    rw [map_sub, map_smul, smul_sub, k2, smul_smul (b - a) c, hbc, one_smul]
    have h3 : c • φ - Ra φ + (Rb φ - (Rb φ - Ra φ)) = c • φ := by abel
    rw [h3, smul_smul, hbc, one_smul]


/-- `S - μ` is bounded below off a finite-dimensional subspace. -/
def FredAt (S : H →L[ℂ] H) (μ : ℂ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ V : Submodule ℂ H, FiniteDimensional ℂ V ∧
    ∀ φ : H, φ ∈ Vᗮ → ε * ‖φ‖ ≤ ‖S φ - μ • φ‖

/-- B1: a compact operator is small off a finite-dimensional subspace. -/
theorem compact_small (C : H →L[ℂ] H) (hC : IsCompactOperator C) (δ : ℝ) (hδ : 0 < δ) :
    ∃ W : Submodule ℂ H, FiniteDimensional ℂ W ∧ ∀ φ : H, φ ∈ Wᗮ → ‖C φ‖ ≤ δ * ‖φ‖ := by
  have hK : IsCompact (closure (C '' Metric.closedBall 0 1)) :=
    hC.isCompact_closure_image_closedBall 1
  obtain ⟨t, htf, hcov⟩ := Metric.totallyBounded_iff.1 hK.totallyBounded δ hδ
  refine ⟨Submodule.span ℂ (ContinuousLinearMap.adjoint C '' t),
    FiniteDimensional.span_of_finite ℂ (htf.image _), ?_⟩
  intro φ hφ
  by_cases h0 : φ = 0
  · simp [h0]
  have hn : 0 < ‖φ‖ := norm_pos_iff.2 h0
  set u : H := ((‖φ‖⁻¹ : ℝ) : ℂ) • φ with hu
  have hu1 : u ∈ Metric.closedBall (0 : H) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, hu, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hn), inv_mul_cancel₀ hn.ne']
  have huW : u ∈ (Submodule.span ℂ (ContinuousLinearMap.adjoint C '' t))ᗮ :=
    Submodule.smul_mem _ _ hφ
  have hmem : C u ∈ ⋃ y ∈ t, Metric.ball y δ := hcov (subset_closure ⟨u, hu1, rfl⟩)
  simp only [Set.mem_iUnion, Metric.mem_ball] at hmem
  obtain ⟨y, hyt, hy⟩ := hmem
  have horth : ⟪C u, y⟫_ℂ = 0 := by
    have h1 : ⟪ContinuousLinearMap.adjoint C y, u⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_image_of_mem _ hyt)) huW
    rw [ContinuousLinearMap.adjoint_inner_left] at h1
    rw [← inner_conj_symm, h1, map_zero]
  have hCu : ‖C u‖ ≤ δ := by
    have h2 : ‖C u‖ ^ 2 ≤ ‖C u‖ * ‖C u - y‖ := by
      have e : (⟪C u, C u - y⟫_ℂ).re = ‖C u‖ ^ 2 := by
        rw [inner_sub_right, horth, sub_zero]
        exact inner_self_eq_norm_sq (𝕜 := ℂ) (C u)
      rw [← e]
      exact (Complex.re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)
    rw [← dist_eq_norm] at h2
    by_cases hz : ‖C u‖ = 0
    · rw [hz]; exact hδ.le
    · have hp : 0 < ‖C u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have : ‖C u‖ ≤ dist (C u) y := by nlinarith
      linarith
  have hφu : φ = ((‖φ‖ : ℝ) : ℂ) • u := by
    rw [hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  rw [hφu, map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  have hu' : ‖u‖ = 1 := by
    rw [hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn),
      inv_mul_cancel₀ hn.ne']
  rw [hu', mul_one, mul_comm]
  exact mul_le_mul_of_nonneg_right hCu hn.le

/-- B1': `FredAt` is stable under compact perturbations. -/
theorem fred_add_compact (S C : H →L[ℂ] H) (hC : IsCompactOperator C) (μ : ℂ)
    (h : FredAt S μ) : FredAt (S + C) μ := by
  obtain ⟨ε, hε, V, hV, hS⟩ := h
  obtain ⟨W, hW, hCW⟩ := compact_small C hC (ε / 2) (by linarith)
  refine ⟨ε / 2, by linarith, V ⊔ W, Submodule.finiteDimensional_sup V W, ?_⟩
  intro φ hφ
  have hφV : φ ∈ Vᗮ := Submodule.orthogonal_le le_sup_left hφ
  have hφW : φ ∈ Wᗮ := Submodule.orthogonal_le le_sup_right hφ
  have h1 := hS φ hφV
  have h2 := hCW φ hφW
  have h3 : ‖S φ - μ • φ‖ ≤ ‖(S + C) φ - μ • φ‖ + ‖C φ‖ := by
    have : S φ - μ • φ = ((S + C) φ - μ • φ) - C φ := by
      simp; abel
    rw [this]; exact norm_sub_le _ _
  linarith

/-- Finite-dimensional bound: a subspace meeting `Vᗮ` trivially has dimension at most `dim V`. -/
theorem dim_le (M V : Submodule ℂ H) [FiniteDimensional ℂ V]
    (h : ∀ x ∈ M, x ∈ Vᗮ → x = 0) :
    FiniteDimensional ℂ M ∧ Module.finrank ℂ M ≤ Module.finrank ℂ V := by
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  set L : M →ₗ[ℂ] V := (V.orthogonalProjectionOnto : H →L[ℂ] V).toLinearMap ∘ₗ M.subtype
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have : (x : H) ∈ Vᗮ := by
      rw [← Submodule.orthogonalProjectionOnto_eq_zero_iff]
      exact hx
    exact Subtype.ext (h x x.2 this)
  haveI : FiniteDimensional ℂ M := Module.Finite.of_injective L hinj
  exact ⟨inferInstance, LinearMap.finrank_le_finrank_of_injective hinj⟩

/-- B2-T1: outside the spectrum, `S - μ` is bounded below. -/
theorem fred_of_not_spec (S : H →L[ℂ] H) (μ : ℂ) (h : μ ∉ spectrum ℂ S) : FredAt S μ := by
  have h' : IsUnit (algebraMap ℂ (H →L[ℂ] H) μ - S) :=
    not_not.1 (fun hc => h (spectrum.mem_iff.2 hc))
  obtain ⟨U, hU⟩ := h'
  set c := ‖(↑U⁻¹ : H →L[ℂ] H)‖ with hcdef
  have hc : 0 ≤ c := norm_nonneg _
  refine ⟨1 / (c + 1), by positivity, ⊥, inferInstance, ?_⟩
  intro φ _
  have e : (↑U⁻¹ : H →L[ℂ] H) (μ • φ - S φ) = φ := by
    have : ((↑U⁻¹ : H →L[ℂ] H) * ↑U) φ = φ := by rw [Units.inv_mul]; rfl
    rw [hU] at this
    simpa [Algebra.algebraMap_eq_smul_one] using this
  have h1 : ‖φ‖ ≤ c * ‖S φ - μ • φ‖ := by
    calc ‖φ‖ = ‖(↑U⁻¹ : H →L[ℂ] H) (μ • φ - S φ)‖ := by rw [e]
      _ ≤ c * ‖μ • φ - S φ‖ := ContinuousLinearMap.le_opNorm _ _
      _ = _ := by rw [norm_sub_rev]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg φ, norm_nonneg (S φ - μ • φ)]

/-- `(S - m) cfc G S = cfc ((t - m) G) S`, pointwise. -/
theorem cfc_lin (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (m : ℝ) (G : ℝ → ℝ) (hG : Continuous G)
    (x : H) :
    S (cfc G S x) - (m : ℂ) • cfc G S x = cfc (fun t => (t - m) * G t) S x := by
  rw [cfc_mul (fun t => t - m) G S (by fun_prop) hG.continuousOn,
    cfc_sub (fun t => t) (fun _ => m) S, cfc_id' ℝ S, cfc_const m S]
  simp [Algebra.algebraMap_eq_smul_one, Complex.coe_smul]

/-- B2-T3(b): a "spectral window" subspace of width `ε/2` around `m` has dimension `≤ dim V`. -/
theorem window_dim (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (m : ℝ) (ε : ℝ) (hε : 0 < ε)
    (V : Submodule ℂ H) [FiniteDimensional ℂ V]
    (hV : ∀ φ : H, φ ∈ Vᗮ → ε * ‖φ‖ ≤ ‖S φ - (m : ℂ) • φ‖)
    (G : ℝ → ℝ) (hG : Continuous G) (hGb : ∀ t, |(t - m) * G t| ≤ ε / 2)
    (M : Submodule ℂ H) (hM : ∀ x ∈ M, cfc G S x = x) :
    FiniteDimensional ℂ M ∧ Module.finrank ℂ M ≤ Module.finrank ℂ V := by
  apply dim_le M V
  intro x hxM hxV
  have h1 := hV x hxV
  have e := cfc_lin S hS m G hG x
  rw [hM x hxM] at e
  have h2 : ‖S x - (m : ℂ) • x‖ ≤ ε / 2 * ‖x‖ := by
    rw [e]
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact norm_cfc_le (by linarith) (fun t _ => by rw [Real.norm_eq_abs]; exact hGb t)
  have : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
  exact norm_eq_zero.1 this

/-- The plateau function: `1` on `|t - m| ≤ ε/4`, `0` for `|t - m| ≥ ε/2`. -/
noncomputable def plateau (m ε : ℝ) (t : ℝ) : ℝ := max 0 (min 1 (2 - 4 * |t - m| / ε))

/-- A tent of radius `r` at `w`. -/
noncomputable def tent (w r : ℝ) (t : ℝ) : ℝ := max 0 (1 - |t - w| / r)

theorem plateau_cont (m ε : ℝ) : Continuous (plateau m ε) := by
  unfold plateau; fun_prop

theorem tent_cont (w r : ℝ) : Continuous (tent w r) := by
  unfold tent; fun_prop

theorem plateau_bound (m ε : ℝ) (hε : 0 < ε) (t : ℝ) : |(t - m) * plateau m ε t| ≤ ε / 2 := by
  unfold plateau
  rw [abs_mul]
  by_cases h : |t - m| < ε / 2
  · have h0 : 0 ≤ max 0 (min 1 (2 - 4 * |t - m| / ε)) := le_max_left _ _
    have h1 : max 0 (min 1 (2 - 4 * |t - m| / ε)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
    rw [abs_of_nonneg h0]
    nlinarith [abs_nonneg (t - m)]
  · have : 2 - 4 * |t - m| / ε ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hε]; linarith
    have : max 0 (min 1 (2 - 4 * |t - m| / ε)) = 0 :=
      max_eq_left ((min_le_right _ _).trans this)
    rw [this]; simp; linarith

theorem tent_eq_zero {w r t : ℝ} (hr : 0 < r) (h : r ≤ |t - w|) : tent w r t = 0 := by
  unfold tent
  apply max_eq_left
  rw [sub_nonpos, le_div_iff₀ hr]; linarith

theorem tent_self (w r : ℝ) (hr : 0 < r) : tent w r w = 1 := by
  unfold tent; simp

/-- B2-T3(c): a finite set of spectral points within `ε/4` of `m` has at most `dim V` elements. -/
theorem card_le (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (m : ℝ) (ε : ℝ) (hε : 0 < ε)
    (V : Submodule ℂ H) [FiniteDimensional ℂ V]
    (hV : ∀ φ : H, φ ∈ Vᗮ → ε * ‖φ‖ ≤ ‖S φ - (m : ℂ) • φ‖)
    (F : Finset ℝ) (hF : ∀ w ∈ F, w ∈ spectrum ℝ S ∧ |w - m| < ε / 4) :
    F.card ≤ Module.finrank ℂ V := by
  classical
  -- a common tent radius
  have hev : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ p ∈ F ×ˢ F,
      (p.1 ≠ p.2 → 2 * r ≤ |p.1 - p.2|) ∧ r ≤ ε / 4 - |p.1 - m| := by
    rw [Filter.eventually_all_finset]
    intro p hp
    rw [Finset.mem_product] at hp
    have hpos : 0 < ε / 4 - |p.1 - m| := by linarith [(hF p.1 hp.1).2]
    refine Filter.Eventually.and ?_ ?_
    · by_cases hne : p.1 = p.2
      · exact Filter.Eventually.of_forall (fun _ h => absurd hne h)
      · have hd : 0 < |p.1 - p.2| / 2 := by
          have : 0 < |p.1 - p.2| := abs_pos.2 (sub_ne_zero.2 hne)
          linarith
        filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hd)] with r hr _
        linarith
    · filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hpos)] with r hr
      exact hr.le
  obtain ⟨r, hr, hrpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hr0 : (0 : ℝ) < r := hrpos
  set G := plateau m ε with hGdef
  -- G * tent = tent
  have hGt : ∀ w ∈ F, ∀ t, G t * tent w r t = tent w r t := by
    intro w hw t
    by_cases ht : |t - w| < r
    · have hwm := (hr (w, w) (Finset.mem_product.2 ⟨hw, hw⟩)).2
      simp only at hwm
      have htm : |t - m| ≤ ε / 4 := by
        have := abs_sub_le t w m
        linarith
      have : G t = 1 := by
        rw [hGdef]; unfold plateau
        have : 1 ≤ 2 - 4 * |t - m| / ε := by
          rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hε]; linarith
        rw [min_eq_left this, max_eq_right zero_le_one]
      rw [this, one_mul]
    · rw [tent_eq_zero hr0 (not_lt.1 ht), mul_zero]
  -- disjoint tents
  have hdis : ∀ w ∈ F, ∀ w' ∈ F, w ≠ w' → ∀ t, tent w r t * tent w' r t = 0 := by
    intro w hw w' hw' hne t
    have hsep := (hr (w, w') (Finset.mem_product.2 ⟨hw, hw'⟩)).1 hne
    simp only at hsep
    by_cases ht : |t - w| < r
    · have : r ≤ |t - w'| := by
        by_contra hc
        push Not at hc
        have := abs_sub_le w t w'
        rw [abs_sub_comm w t] at this
        linarith
      rw [tent_eq_zero hr0 this, mul_zero]
    · rw [tent_eq_zero hr0 (not_lt.1 ht), zero_mul]
  -- nonzero vectors in the range of each tent
  have hne : ∀ w ∈ F, ∃ η : H, cfc (tent w r) S η ≠ 0 := by
    intro w hw
    by_contra hc
    push Not at hc
    have h0 : cfc (tent w r) S = 0 := ContinuousLinearMap.ext hc
    have := norm_apply_le_norm_cfc (tent w r) S (hF w hw).1 (tent_cont w r).continuousOn hS
    rw [h0, tent_self w r hr0, norm_zero] at this
    norm_num at this
  choose! η hη using hne
  set v : F → H := fun w => cfc (tent w r) S (η w) with hv
  have hv0 : ∀ w : F, v w ≠ 0 := fun w => hη w w.2
  have hvG : ∀ w : F, cfc G S (v w) = v w := by
    intro w
    rw [hv]
    show (cfc G S * cfc (tent (w : ℝ) r) S) (η w) = _
    rw [← cfc_mul G (tent (w : ℝ) r) S (plateau_cont m ε).continuousOn
      (tent_cont _ r).continuousOn]
    congr 2
    funext t
    exact hGt w w.2 t
  have hvo : Pairwise fun i j : F => ⟪v i, v j⟫_ℂ = 0 := by
    intro i j hij
    have hij' : (i : ℝ) ≠ j := fun h => hij (Subtype.ext h)
    have hsa : IsSelfAdjoint (cfc (tent (i : ℝ) r) S) := cfc_predicate _ _
    rw [hv]
    simp only
    rw [← ContinuousLinearMap.adjoint_inner_right (cfc (tent (i : ℝ) r) S),
      ← ContinuousLinearMap.star_eq_adjoint, hsa.star_eq]
    show ⟪η i, (cfc (tent (i : ℝ) r) S * cfc (tent (j : ℝ) r) S) (η j)⟫_ℂ = 0
    rw [← cfc_mul _ _ S (tent_cont _ r).continuousOn (tent_cont _ r).continuousOn]
    have : (fun t => tent (i : ℝ) r t * tent (j : ℝ) r t) = fun _ => 0 := by
      funext t; exact hdis i i.2 j j.2 hij' t
    rw [this, cfc_const_zero]
    simp
  have hli : LinearIndependent ℂ v := linearIndependent_of_ne_zero_of_inner_eq_zero hv0 hvo
  set M : Submodule ℂ H := LinearMap.ker (((cfc G S : H →L[ℂ] H) : H →ₗ[ℂ] H) - LinearMap.id) with hMdef
  have hMmem : ∀ x ∈ M, cfc G S x = x := by
    intro x hx
    rw [hMdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hx
    exact hx
  obtain ⟨hMf, hMr⟩ := window_dim S hS m ε hε V hV G (plateau_cont m ε)
    (plateau_bound m ε hε) M hMmem
  have hvM : ∀ w : F, v w ∈ M := by
    intro w
    rw [hMdef, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    exact hvG w
  set v' : F → M := fun w => ⟨v w, hvM w⟩
  have hli' : LinearIndependent ℂ v' := by
    apply LinearIndependent.of_comp M.subtype
    exact hli
  have := hli'.fintype_card_le_finrank
  rw [Fintype.card_coe] at this
  exact this.trans hMr

/-- The eigenspace of a bounded operator. -/
def eig (S : H →L[ℂ] H) (μ : ℂ) : Submodule ℂ H :=
  LinearMap.ker ((S : H →ₗ[ℂ] H) - μ • LinearMap.id)

theorem mem_eig {S : H →L[ℂ] H} {μ : ℂ} {φ : H} : φ ∈ eig S μ ↔ S φ = μ • φ := by
  rw [eig, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  rfl

/-- B2-T3: `FredAt` at a spectral point forces a discrete eigenvalue. -/
theorem of_fred (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (μ : ℂ) (h : FredAt S μ)
    (hμ : μ ∈ spectrum ℂ S) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ spectrum ℂ S, ‖w - μ‖ < δ → w = μ) ∧ eig S μ ≠ ⊥ ∧
      FiniteDimensional ℂ (eig S μ) := by
  classical
  obtain ⟨ε, hε, V, hV, hfred⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m : ℝ, μ = m := ⟨μ.re, hS.mem_spectrum_eq_re hμ⟩
  have hreal : ∀ w ∈ spectrum ℂ S, w = (w.re : ℂ) := fun w hw => hS.mem_spectrum_eq_re hw
  have hRe : ∀ w ∈ spectrum ℂ S, w.re ∈ spectrum ℝ S := by
    intro w hw
    apply spectrum.of_algebraMap_mem ℂ
    have e : (algebraMap ℝ ℂ) w.re = w := by
      rw [Complex.coe_algebraMap]; exact (hreal w hw).symm
    rw [e]; exact hw
  -- finiteness of the spectrum near m
  set P : Set ℝ := {w | w ∈ spectrum ℝ S ∧ |w - m| < ε / 4} with hPdef
  have hPfin : P.Finite := by
    by_contra hinf
    obtain ⟨F, hFsub, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf (Module.finrank ℂ V + 1)
    have := card_le S hS m ε hε V hfred F (fun w hw => hFsub hw)
    omega
  set T := hPfin.toFinset.erase m with hTdef
  have hev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ w ∈ T, δ ≤ |w - m| := by
    rw [Filter.eventually_all_finset]
    intro w hw
    have hpos : 0 < |w - m| := abs_pos.2 (sub_ne_zero.2 (Finset.ne_of_mem_erase hw))
    filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hpos)] with δ hδ
    exact hδ.le
  have hev2 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ < ε / 4 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by linarith))
  obtain ⟨δ, ⟨hδT, hδε⟩, hδpos⟩ := ((hev.and hev2).and self_mem_nhdsWithin).exists
  have hδ0 : (0 : ℝ) < δ := hδpos
  have hiso : ∀ w ∈ spectrum ℂ S, ‖w - (m : ℂ)‖ < δ → w = m := by
    intro w hw hwd
    have e := hreal w hw
    have hn : ‖w - (m : ℂ)‖ = |w.re - m| := by
      rw [e, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
    rw [hn] at hwd
    by_contra hne
    have hre : w.re ≠ m := fun h' => hne (by rw [e, h'])
    have hP : w.re ∈ P := ⟨hRe w hw, by linarith⟩
    have hT : w.re ∈ T := Finset.mem_erase.2 ⟨hre, hPfin.mem_toFinset.2 hP⟩
    have := hδT w.re hT
    linarith
  refine ⟨⟨δ, hδ0, hiso⟩, ?_, ?_⟩
  · -- an eigenvector from the tent at `m`
    have hmS : m ∈ spectrum ℝ S := by
      have := hRe _ hμ
      simpa using this
    have hne : ∃ η : H, cfc (tent m δ) S η ≠ 0 := by
      by_contra hc
      push Not at hc
      have h0 : cfc (tent m δ) S = 0 := ContinuousLinearMap.ext hc
      have := norm_apply_le_norm_cfc (tent m δ) S hmS (tent_cont m δ).continuousOn hS
      rw [h0, tent_self m δ hδ0, norm_zero] at this
      norm_num at this
    obtain ⟨η, hη⟩ := hne
    have hzero : cfc (fun t => (t - m) * tent m δ t) S = 0 := by
      rw [← cfc_const_zero (R := ℝ) (a := S)]
      apply cfc_congr
      intro t ht
      by_cases htm : t = m
      · simp [htm]
      · have htC : (t : ℂ) ∈ spectrum ℂ S := by
          have := spectrum.algebraMap_mem ℂ ht
          simpa using this
        have : δ ≤ |t - m| := by
          by_contra hc
          push Not at hc
          have := hiso _ htC (by
            rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hc)
          exact htm (Complex.ofReal_injective this)
        simp [tent_eq_zero hδ0 this]
    have e := cfc_lin S hS m (tent m δ) (tent_cont m δ) η
    rw [hzero, ContinuousLinearMap.zero_apply, sub_eq_zero] at e
    rw [Submodule.ne_bot_iff]
    exact ⟨cfc (tent m δ) S η, mem_eig.2 e, hη⟩
  · haveI := hV
    refine (dim_le (eig S m) V ?_).1
    intro x hx hxV
    have h1 := hfred x hxV
    rw [mem_eig.1 hx, sub_self, norm_zero] at h1
    have : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.1 this

/-- B2-T2: at an isolated eigenvalue of finite multiplicity, `FredAt` holds. -/
theorem fred_of_discrete (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (μ : ℂ)
    (hμ : μ ∈ spectrum ℂ S) (δ : ℝ) (hδ : 0 < δ)
    (hiso : ∀ w ∈ spectrum ℂ S, ‖w - μ‖ < δ → w = μ) (hfin : FiniteDimensional ℂ (eig S μ)) :
    FredAt S μ := by
  obtain ⟨m, rfl⟩ : ∃ m : ℝ, μ = m := ⟨μ.re, hS.mem_spectrum_eq_re hμ⟩
  have hfar : ∀ t ∈ spectrum ℝ S, t ≠ m → δ ≤ |t - m| := by
    intro t ht htm
    have htC : (t : ℂ) ∈ spectrum ℂ S := by
      have := spectrum.algebraMap_mem ℂ ht
      simpa using this
    by_contra hc
    push Not at hc
    have := hiso _ htC (by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hc)
    exact htm (Complex.ofReal_injective this)
  set Q := cfc (tent m δ) S with hQdef
  have hden : ∀ t : ℝ, max ((t - m) ^ 2) (δ ^ 2) ≠ 0 := fun t =>
    (lt_of_lt_of_le (by positivity) (le_max_right _ _)).ne'
  set g : ℝ → ℝ := fun t => (t - m) * (max ((t - m) ^ 2) (δ ^ 2))⁻¹ with hgdef
  have hgc : Continuous g :=
    (continuous_id.sub continuous_const).mul
      ((by fun_prop : Continuous fun t : ℝ => max ((t - m) ^ 2) (δ ^ 2)).inv₀ hden)
  have hlin : cfc (fun t : ℝ => t - m) S = S - algebraMap ℝ (H →L[ℂ] H) m := by
    rw [cfc_sub (fun t : ℝ => t) (fun _ => m) S, cfc_id' ℝ S, cfc_const m S]
  have hkey : cfc g S * cfc (fun t : ℝ => t - m) S = 1 - Q := by
    rw [← cfc_mul g (fun t : ℝ => t - m) S hgc.continuousOn (by fun_prop), hQdef,
      ← cfc_const_one (R := ℝ) (a := S),
      ← cfc_sub (fun _ : ℝ => (1 : ℝ)) (tent m δ) S (by fun_prop) (tent_cont m δ).continuousOn]
    apply cfc_congr
    intro t ht
    by_cases htm : t = m
    · simp [hgdef, htm, tent_self m δ hδ]
    · have h1 := hfar t ht htm
      have h2 : δ ^ 2 ≤ (t - m) ^ 2 := by
        rw [← sq_abs (t - m)]; exact pow_le_pow_left₀ hδ.le h1 2
      have hne : (t - m) ≠ 0 := sub_ne_zero.2 htm
      simp only [hgdef]
      rw [max_eq_left h2, tent_eq_zero hδ h1, sub_zero]
      field_simp
  have hQeig : ∀ η : H, Q η ∈ eig S m := by
    intro η
    have hzero : cfc (fun t => (t - m) * tent m δ t) S = 0 := by
      rw [← cfc_const_zero (R := ℝ) (a := S)]
      apply cfc_congr
      intro t ht
      by_cases htm : t = m
      · simp [htm]
      · simp [tent_eq_zero hδ (hfar t ht htm)]
    have e := cfc_lin S hS m (tent m δ) (tent_cont m δ) η
    rw [hzero, ContinuousLinearMap.zero_apply, sub_eq_zero] at e
    exact mem_eig.2 e
  have hsa : IsSelfAdjoint Q := cfc_predicate _ _
  set c := ‖cfc g S‖ with hcdef
  have hc : 0 ≤ c := norm_nonneg _
  refine ⟨1 / (c + 1), by positivity, eig S m, hfin, ?_⟩
  intro φ hφ
  have hQφ : Q φ = 0 := by
    have : ⟪Q φ, Q φ⟫_ℂ = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_right Q, ← ContinuousLinearMap.star_eq_adjoint,
        hsa.star_eq]
      exact Submodule.inner_left_of_mem_orthogonal (hQeig (Q φ)) hφ
    exact inner_self_eq_zero.1 this
  have e : cfc g S (S φ - (m : ℂ) • φ) = φ := by
    have h1 : (cfc g S * cfc (fun t : ℝ => t - m) S) φ = φ - Q φ := by
      rw [hkey]; simp
    rw [hQφ, sub_zero, ContinuousLinearMap.mul_apply, hlin] at h1
    have h2 : (S - algebraMap ℝ (H →L[ℂ] H) m) φ = S φ - (m : ℂ) • φ := by
      simp [Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
    rw [h2] at h1
    exact h1
  have h1 : ‖φ‖ ≤ c * ‖S φ - (m : ℂ) • φ‖ := by
    calc ‖φ‖ = ‖cfc g S (S φ - (m : ℂ) • φ)‖ := by rw [e]
      _ ≤ c * ‖S φ - (m : ℂ) • φ‖ := ContinuousLinearMap.le_opNorm _ _
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg φ, norm_nonneg (S φ - (m : ℂ) • φ)]



/-- An inverse of `ν - R` (with `ν = (w - l)⁻¹`, `R = R_X(l)`) yields a resolvent of `X` at `w`. -/
theorem resolvent_of_inv (X : H →ₗ.[ℂ] H) (l w : ℂ) (R V : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt X l R) (hwν : (w - l) * (w - l)⁻¹ = 1)
    (h1 : ∀ x, (w - l)⁻¹ • V x - R (V x) = x) (h2 : ∀ x, V ((w - l)⁻¹ • x - R x) = x) :
    TeschlQM.Shared.IsResolventAt X w (R.comp ((w - l)⁻¹ • V)) := by
  have hcomm : ∀ x, R (V x) = V (R x) := by
    intro x
    have e : (w - l)⁻¹ • R (V x) - R (R (V x)) = R x := by
      conv_rhs => rw [← h1 x]
      rw [map_sub, map_smul]
    calc R (V x) = V ((w - l)⁻¹ • R (V x) - R (R (V x))) := (h2 _).symm
      _ = V (R x) := by rw [e]
  refine ⟨fun φ => ?_, fun ψ => ?_⟩
  · obtain ⟨hd, he⟩ := hR.1 ((w - l)⁻¹ • V φ)
    refine ⟨hd, ?_⟩
    show X ⟨R ((w - l)⁻¹ • V φ), hd⟩ - w • R ((w - l)⁻¹ • V φ) = φ
    have hX : X ⟨R ((w - l)⁻¹ • V φ), hd⟩ = (w - l)⁻¹ • V φ + l • R ((w - l)⁻¹ • V φ) :=
      eq_add_of_sub_eq he
    have key : l • ((w - l)⁻¹ • R (V φ)) - w • ((w - l)⁻¹ • R (V φ)) = - R (V φ) := by
      rw [smul_smul, smul_smul, ← sub_smul,
        show l * (w - l)⁻¹ - w * (w - l)⁻¹ = -((w - l) * (w - l)⁻¹) by ring, hwν, neg_one_smul]
    rw [hX, map_smul, add_sub_assoc, key, ← sub_eq_add_neg]
    exact h1 φ
  · have e2 : R (X ψ - l • (ψ : H)) = ψ := hR.2 ψ
    have hu : R (X ψ - w • (ψ : H)) = (w - l) • ((w - l)⁻¹ • (ψ : H) - R ψ) := by
      have : X ψ - w • (ψ : H) = (X ψ - l • (ψ : H)) - (w - l) • (ψ : H) := by
        rw [sub_smul]; abel
      rw [this, map_sub, e2, map_smul, smul_sub, smul_smul, hwν, one_smul]
    show R ((w - l)⁻¹ • V (X ψ - w • (ψ : H))) = ψ
    rw [map_smul, hcomm, hu, map_smul, h2, smul_smul, mul_comm, hwν, one_smul]

/-- `ν - R` invertible gives a resolvent at `w`. -/
theorem resolvent_of_unit (X : H →ₗ.[ℂ] H) (l w : ℂ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt X l R) (hw : w ≠ l)
    (hu : IsUnit (algebraMap ℂ (H →L[ℂ] H) ((w - l)⁻¹) - R)) :
    ∃ S : H →L[ℂ] H, TeschlQM.Shared.IsResolventAt X w S := by
  obtain ⟨U, hU⟩ := hu
  have hwν : (w - l) * (w - l)⁻¹ = 1 := mul_inv_cancel₀ (sub_ne_zero.2 hw)
  refine ⟨_, resolvent_of_inv X l w R (↑U⁻¹ : H →L[ℂ] H) hR hwν (fun x => ?_) (fun x => ?_)⟩
  · have := congrArg (fun T : H →L[ℂ] H => T x) U.mul_inv
    simpa [hU, Algebra.algebraMap_eq_smul_one] using this
  · have := congrArg (fun T : H →L[ℂ] H => T x) U.inv_mul
    simpa [hU, Algebra.algebraMap_eq_smul_one] using this

/-- Spectral mapping for the resolvent: `w ∈ σ(X) ↔ (w - l)⁻¹ ∈ σ(R_X(l))`. -/
theorem spec_iff (X : H →ₗ.[ℂ] H) (l w : ℂ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt X l R) (hw : w ≠ l) :
    w ∈ TeschlQM.Shared.spectrum X ↔ (w - l)⁻¹ ∈ spectrum ℂ R := by
  unfold TeschlQM.Shared.spectrum
  rw [Set.mem_compl_iff, spectrum.mem_iff]
  constructor
  · intro hs hu
    exact hs (by exact resolvent_of_unit X l w R hR hw hu)
  · intro hn hres
    obtain ⟨Rw, hRw⟩ := hres
    exact hn (isUnit_of_resolvent X l w (Ne.symm hw) R Rw hR hRw)

theorem mem_eigenspace {X : H →ₗ.[ℂ] H} {μ : ℂ} {φ : H} :
    φ ∈ TeschlQM.Shared.eigenspace X μ ↔ ∃ h : φ ∈ X.domain, X ⟨φ, h⟩ = μ • φ := by
  unfold TeschlQM.Shared.eigenspace
  constructor
  · rintro ⟨⟨ψ, hψd⟩, hψ, rfl⟩
    refine ⟨hψd, ?_⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hψ
    simpa [sub_eq_zero] using hψ
  · rintro ⟨h, hX⟩
    refine ⟨⟨φ, h⟩, ?_, rfl⟩
    simp [hX]

/-- Eigenvectors of `X` at `μ` are eigenvectors of `R_X(l)` at `(μ - l)⁻¹`. -/
theorem eig_iff (X : H →ₗ.[ℂ] H) (l μ : ℂ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt X l R) (hμ : μ ≠ l) (φ : H) :
    φ ∈ TeschlQM.Shared.eigenspace X μ ↔ R φ = (μ - l)⁻¹ • φ := by
  have hc : μ - l ≠ 0 := sub_ne_zero.2 hμ
  rw [mem_eigenspace]
  constructor
  · rintro ⟨h, hX⟩
    have e2 : R (X ⟨φ, h⟩ - l • φ) = φ := hR.2 ⟨φ, h⟩
    rw [hX, ← sub_smul, map_smul] at e2
    calc R φ = (μ - l)⁻¹ • ((μ - l) • R φ) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = (μ - l)⁻¹ • φ := by rw [e2]
  · intro hRφ
    obtain ⟨hd, he⟩ := hR.1 φ
    have hφ : φ = (μ - l) • R φ := by rw [hRφ, smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hdφ : φ ∈ X.domain := by rw [hφ]; exact X.domain.smul_mem _ hd
    refine ⟨hdφ, ?_⟩
    have e : (⟨φ, hdφ⟩ : X.domain) = (μ - l) • (⟨R φ, hd⟩ : X.domain) := Subtype.ext hφ
    have hX : X ⟨R φ, hd⟩ = φ + l • R φ := eq_add_of_sub_eq he
    rw [e, LinearPMap.map_smul, hX, hRφ, smul_add, smul_smul, smul_smul, ← add_smul]
    congr 1
    have hmi : (μ - l) * (μ - l)⁻¹ = 1 := mul_inv_cancel₀ hc
    linear_combination l * hmi

theorem eig_eq (X : H →ₗ.[ℂ] H) (l μ : ℂ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt X l R) (hμ : μ ≠ l) :
    TeschlQM.Shared.eigenspace X μ = eig R ((μ - l)⁻¹) :=
  Submodule.ext fun φ => (eig_iff X l μ R hR hμ φ).trans mem_eig.symm

theorem not_spec_at (X : H →ₗ.[ℂ] H) (l : ℂ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt X l R) : l ∉ TeschlQM.Shared.spectrum X := by
  unfold TeschlQM.Shared.spectrum
  rw [Set.mem_compl_iff, not_not]
  exact (⟨R, hR⟩ : ∃ S : H →L[ℂ] H, TeschlQM.Shared.IsResolventAt X l S)

theorem not_ess_at (X : H →ₗ.[ℂ] H) (l : ℂ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt X l R) :
    l ∉ TeschlQM.Shared.essentialSpectrum X := fun h => not_spec_at X l R hR h.1


/-! ## Complex resolvent points: the resolvent is normal -/

/-- For self-adjoint `A`, `R_A(z)† = R_A(z̄)`. -/
theorem star_resolvent (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A z R) :
    TeschlQM.Shared.IsResolventAt A (starRingEnd ℂ z) (ContinuousLinearMap.adjoint R) := by
  have hs := symm_of_selfAdjoint A hA
  have hA' : A† = A := hA
  refine ⟨fun x => ?_, fun ψ => ?_⟩
  · have hw : ∀ ψ : A.domain, ⟪x + (starRingEnd ℂ z) • ContinuousLinearMap.adjoint R x, (ψ : H)⟫_ℂ =
        ⟪ContinuousLinearMap.adjoint R x, A ψ⟫_ℂ := by
      intro ψ
      have e2 : R (A ψ - z • (ψ : H)) = ψ := hR.2 ψ
      rw [map_sub, map_smul] at e2
      have hRA : R (A ψ) = (ψ : H) + z • R ψ := eq_add_of_sub_eq e2
      rw [ContinuousLinearMap.adjoint_inner_left, hRA, inner_add_left, inner_smul_left,
        inner_add_right, inner_smul_right, ContinuousLinearMap.adjoint_inner_left]
      simp
    have hmem : ContinuousLinearMap.adjoint R x ∈ A†.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨_, hw⟩
    have hd : ContinuousLinearMap.adjoint R x ∈ A.domain := by rw [hA'] at hmem; exact hmem
    have hle : A† ≤ A := by rw [hA']
    have h1 : A† ⟨_, hmem⟩ = A ⟨_, hd⟩ := hle.2 (x := ⟨_, hmem⟩) (y := ⟨_, hd⟩) rfl
    have h2 := LinearPMap.adjoint_apply_eq hA.dense_domain ⟨_, hmem⟩ hw
    refine ⟨hd, ?_⟩
    rw [← h1, h2, add_sub_cancel_right]
  · apply ext_inner_right ℂ
    intro y
    obtain ⟨hu, he⟩ := hR.1 y
    have hAu : A ⟨R y, hu⟩ = y + z • R y := eq_add_of_sub_eq he
    rw [ContinuousLinearMap.adjoint_inner_left, inner_sub_left, inner_smul_left,
      hs ψ ⟨R y, hu⟩, hAu, inner_add_right, inner_smul_right]
    simp

/-- The resolvent of a self-adjoint operator at any point of `ρ(A)` is normal. -/
theorem resolvent_normal (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (z : ℂ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A z R) : IsStarNormal R := by
  have hS := star_resolvent A hA z R hR
  have h1 := fun φ => resolvent_identity A z (starRingEnd ℂ z) R _ hR hS φ
  have h2 := fun φ => resolvent_identity A (starRingEnd ℂ z) z _ R hS hR φ
  refine ⟨?_⟩
  show star R * R = R * star R
  ext φ
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint]
  by_cases hz : z - starRingEnd ℂ z = 0
  · have e : ∀ ψ, R ψ = (ContinuousLinearMap.adjoint R) ψ := fun ψ => by
      have := h1 ψ; rw [hz, zero_smul, sub_eq_zero] at this; exact this
    rw [← e (R φ), ← e φ]
  · have e3 : R φ - ContinuousLinearMap.adjoint R φ =
        (z - starRingEnd ℂ z) • ContinuousLinearMap.adjoint R (R φ) := by
      rw [← neg_sub (ContinuousLinearMap.adjoint R φ) (R φ), h2 φ, ← neg_smul, neg_sub]
    apply smul_right_injective H hz
    simp only
    rw [← e3, h1 φ]

/-! ## Normal bounded operators: reduce to `|N - μ|²` -/

theorem dsq (D : H →L[ℂ] H) (φ : H) :
    ‖D φ‖ ^ 2 ≤ ‖φ‖ * ‖(star D * D) φ‖ := by
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    @norm_sq_eq_re_inner ℂ, ← ContinuousLinearMap.adjoint_inner_right]
  exact re_inner_le_norm _ _

theorem fred_iff_T (N : H →L[ℂ] H) (μ : ℂ) :
    FredAt N μ ↔ FredAt (star (N - algebraMap ℂ (H →L[ℂ] H) μ) *
      (N - algebraMap ℂ (H →L[ℂ] H) μ)) 0 := by
  set D := N - algebraMap ℂ (H →L[ℂ] H) μ with hD
  have hDφ : ∀ φ, D φ = N φ - μ • φ := fun φ => by
    simp [hD, Algebra.algebraMap_eq_smul_one]
  constructor
  · rintro ⟨ε, hε, V, hV, hf⟩
    refine ⟨ε ^ 2, by positivity, V, hV, fun φ hφ => ?_⟩
    rw [zero_smul, sub_zero]
    have h1 := hf φ hφ
    rw [← hDφ] at h1
    have h2 := dsq D φ
    have h3 : (ε * ‖φ‖) ^ 2 ≤ ‖D φ‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    rcases (norm_nonneg φ).eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · nlinarith [norm_nonneg ((star D * D) φ)]
  · rintro ⟨ε, hε, V, hV, hf⟩
    refine ⟨ε / (‖star D‖ + 1), by positivity, V, hV, fun φ hφ => ?_⟩
    have h1 := hf φ hφ
    rw [zero_smul, sub_zero, ContinuousLinearMap.mul_apply] at h1
    have h2 : ‖(star D) (D φ)‖ ≤ ‖star D‖ * ‖D φ‖ := (star D).le_opNorm _
    rw [← hDφ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (D φ), norm_nonneg (star D)]

theorem eig_T (N : H →L[ℂ] H) (μ : ℂ) :
    eig (star (N - algebraMap ℂ (H →L[ℂ] H) μ) * (N - algebraMap ℂ (H →L[ℂ] H) μ)) 0 =
      eig N μ := by
  set D := N - algebraMap ℂ (H →L[ℂ] H) μ with hD
  have hDφ : ∀ φ, D φ = N φ - μ • φ := fun φ => by
    simp [hD, Algebra.algebraMap_eq_smul_one]
  ext φ
  rw [mem_eig, mem_eig, zero_smul]
  constructor
  · intro h
    have h2 := dsq D φ
    rw [h, norm_zero, mul_zero] at h2
    have : D φ = 0 := by
      have := pow_eq_zero_iff (n := 2) (two_ne_zero) |>.1 (le_antisymm h2 (by positivity))
      exact norm_eq_zero.1 this
    rw [hDφ, sub_eq_zero] at this
    exact this
  · intro h
    have : D φ = 0 := by rw [hDφ, h, sub_self]
    rw [ContinuousLinearMap.mul_apply, this, map_zero]

theorem spec_T (N : H →L[ℂ] H) (hN : IsStarNormal N) (μ : ℂ) :
    spectrum ℂ (star (N - algebraMap ℂ (H →L[ℂ] H) μ) * (N - algebraMap ℂ (H →L[ℂ] H) μ)) =
      (fun w : ℂ => star (w - μ) * (w - μ)) '' spectrum ℂ N := by
  have e : cfc (fun w : ℂ => star (w - μ) * (w - μ)) N =
      star (N - algebraMap ℂ (H →L[ℂ] H) μ) * (N - algebraMap ℂ (H →L[ℂ] H) μ) := by
    rw [cfc_mul (fun w : ℂ => star (w - μ)) (fun w : ℂ => w - μ) N,
      cfc_star (fun w : ℂ => w - μ) N, cfc_sub (f := fun w : ℂ => w) (g := fun _ => μ) (a := N),
      cfc_id' ℂ N, cfc_const μ N]
  rw [← e, cfc_map_spectrum (fun w : ℂ => star (w - μ) * (w - μ)) N]

theorem norm_f (w μ : ℂ) : ‖star (w - μ) * (w - μ)‖ = ‖w - μ‖ ^ 2 := by
  rw [norm_mul, norm_star, sq]

theorem of_fredN (S : H →L[ℂ] H) (hS : IsStarNormal S) (μ : ℂ) (h : FredAt S μ)
    (hμ : μ ∈ spectrum ℂ S) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ spectrum ℂ S, ‖w - μ‖ < δ → w = μ) ∧ eig S μ ≠ ⊥ ∧
      FiniteDimensional ℂ (eig S μ) := by
  set T := star (S - algebraMap ℂ (H →L[ℂ] H) μ) * (S - algebraMap ℂ (H →L[ℂ] H) μ) with hT
  have hTs : IsSelfAdjoint T := IsSelfAdjoint.star_mul_self _
  have h0 : (0 : ℂ) ∈ spectrum ℂ T := by
    rw [hT, spec_T S hS μ]; exact ⟨μ, hμ, by simp⟩
  obtain ⟨⟨δ, hδ, hiso⟩, hne, hfin⟩ := of_fred T hTs 0 ((fred_iff_T S μ).1 h) h0
  rw [hT, eig_T] at hne hfin
  refine ⟨⟨min δ 1, lt_min hδ one_pos, fun w hw hwd => ?_⟩, hne, hfin⟩
  have hwT : star (w - μ) * (w - μ) ∈ spectrum ℂ T := by
    rw [hT, spec_T S hS μ]; exact ⟨w, hw, rfl⟩
  have hn0 : 0 ≤ ‖w - μ‖ := norm_nonneg _
  have hlt : ‖star (w - μ) * (w - μ) - 0‖ < δ := by
    rw [sub_zero, norm_f]
    have h1 := lt_of_lt_of_le hwd (min_le_left _ _)
    have h2 := lt_of_lt_of_le hwd (min_le_right _ _)
    nlinarith
  have := hiso _ hwT hlt
  have h3 : ‖w - μ‖ ^ 2 = 0 := by rw [← norm_f, this, norm_zero]
  have : ‖w - μ‖ = 0 := pow_eq_zero_iff two_ne_zero |>.1 h3
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

theorem fred_of_discreteN (S : H →L[ℂ] H) (hS : IsStarNormal S) (μ : ℂ)
    (hμ : μ ∈ spectrum ℂ S) (δ : ℝ) (hδ : 0 < δ)
    (hiso : ∀ w ∈ spectrum ℂ S, ‖w - μ‖ < δ → w = μ) (hfin : FiniteDimensional ℂ (eig S μ)) :
    FredAt S μ := by
  set T := star (S - algebraMap ℂ (H →L[ℂ] H) μ) * (S - algebraMap ℂ (H →L[ℂ] H) μ) with hT
  have hTs : IsSelfAdjoint T := IsSelfAdjoint.star_mul_self _
  have h0 : (0 : ℂ) ∈ spectrum ℂ T := by
    rw [hT, spec_T S hS μ]; exact ⟨μ, hμ, by simp⟩
  rw [fred_iff_T S μ]
  refine fred_of_discrete T hTs 0 h0 (δ ^ 2) (by positivity) (fun t ht htd => ?_)
    (by rw [hT, eig_T]; exact hfin)
  rw [hT, spec_T S hS μ] at ht
  obtain ⟨w, hw, rfl⟩ := ht
  rw [sub_zero, norm_f] at htd
  have : ‖w - μ‖ < δ := by nlinarith [norm_nonneg (w - μ)]
  rw [hiso w hw this]; simp

/-- For `μ ≠ l`, `μ ∈ σ_ess(X)` iff `R_X(l) - (μ - l)⁻¹` is not Fredholm-like (normal `R`). -/
theorem ess_iff (X : H →ₗ.[ℂ] H) (l : ℂ) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt X l R) (hRs : IsStarNormal R) (μ : ℂ) (hμ : μ ≠ l) :
    μ ∈ TeschlQM.Shared.essentialSpectrum X ↔ ¬ FredAt R ((μ - l)⁻¹) := by
  have hc : μ - l ≠ 0 := sub_ne_zero.2 hμ
  have heq := eig_eq X l μ R hR hμ
  unfold TeschlQM.Shared.essentialSpectrum TeschlQM.Shared.discreteSpectrum
  constructor
  · rintro ⟨hs, hnd⟩ hF
    have hνs := (spec_iff X l μ R hR hμ).1 hs
    obtain ⟨⟨δ, hδ, hiso⟩, hne, hfin⟩ := of_fredN R hRs _ hF hνs
    apply hnd
    rw [Set.mem_setOf_eq]
    refine ⟨hs, by rw [heq]; exact hne, ?_, by rw [heq]; exact hfin⟩
    have hcont : ContinuousAt (fun w : ℂ => (w - l)⁻¹) μ :=
      (continuousAt_id.sub continuousAt_const).inv₀ hc
    obtain ⟨η, hη, hηc⟩ := Metric.continuousAt_iff.1 hcont δ hδ
    refine ⟨η, hη, fun w hw hwμ => ?_⟩
    have hwl : w ≠ l := fun h => not_spec_at X l R hR (h ▸ hw)
    have hws := (spec_iff X l w R hR hwl).1 hw
    have hd : dist ((w - l)⁻¹) ((μ - l)⁻¹) < δ := hηc (by rw [dist_eq_norm]; exact hwμ)
    rw [dist_eq_norm] at hd
    have := hiso _ hws hd
    exact sub_left_inj.1 (inv_inj.1 this)
  · intro hnF
    have hs : μ ∈ TeschlQM.Shared.spectrum X := by
      by_contra hs
      exact hnF (fred_of_not_spec R _ (fun h => hs ((spec_iff X l μ R hR hμ).2 h)))
    refine ⟨hs, ?_⟩
    rintro ⟨-, -, ⟨ε, hε, hiso⟩, hfin⟩
    have hνs := (spec_iff X l μ R hR hμ).1 hs
    have hν0 : (μ - l)⁻¹ ≠ 0 := inv_ne_zero hc
    have hcont : ContinuousAt (fun v : ℂ => l + v⁻¹) ((μ - l)⁻¹) :=
      continuousAt_const.add (continuousAt_id.inv₀ hν0)
    obtain ⟨η, hη, hηc⟩ := Metric.continuousAt_iff.1 hcont ε hε
    have hpos : 0 < ‖(μ - l)⁻¹‖ := norm_pos_iff.2 hν0
    apply hnF
    refine fred_of_discreteN R hRs _ hνs (min η ‖(μ - l)⁻¹‖) (lt_min hη hpos) ?_
      (by rw [← heq]; exact hfin)
    intro v hv hvd
    have hv0 : v ≠ 0 := by
      rintro rfl
      have := lt_of_lt_of_le hvd (min_le_right _ _)
      simp at this
    have hwl : l + v⁻¹ ≠ l := by simpa using inv_ne_zero hv0
    have hvs : l + v⁻¹ ∈ TeschlQM.Shared.spectrum X := by
      rw [spec_iff X l _ R hR hwl, add_sub_cancel_left, inv_inv]; exact hv
    have hd : dist (l + v⁻¹) (l + ((μ - l)⁻¹)⁻¹) < ε :=
      hηc (by rw [dist_eq_norm]; exact lt_of_lt_of_le hvd (min_le_left _ _))
    rw [inv_inv, add_sub_cancel, dist_eq_norm] at hd
    have h1 := hiso _ hvs hd
    have h2 : v⁻¹ = μ - l := by rw [← h1]; ring
    rw [← h2, inv_inv]


end WeylP

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (h : ∃ (z : ℂ) (RA RB : H →L[ℂ] H), TeschlQM.Shared.IsResolventAt A z RA ∧ TeschlQM.Shared.IsResolventAt B z RB ∧
      IsCompactOperator (RA - RB)) :
    TeschlQM.Shared.essentialSpectrum A = TeschlQM.Shared.essentialSpectrum B := by
  obtain ⟨z, RA, RB, hRA, hRB, hK⟩ := h
  have nA := WeylP.resolvent_normal A hA z RA hRA
  have nB := WeylP.resolvent_normal B hB z RB hRB
  have hK' : IsCompactOperator (RB - RA) := by
    have e : (⇑(RB - RA) : H → H) = -⇑(RA - RB) := by
      ext x; simp
    rw [e]; exact hK.neg
  ext μ
  by_cases hμ : μ = z
  · subst hμ
    exact ⟨fun h => absurd h (WeylP.not_ess_at A μ RA hRA), fun h => absurd h (WeylP.not_ess_at B μ RB hRB)⟩
  · rw [WeylP.ess_iff A z RA hRA nA μ hμ, WeylP.ess_iff B z RB hRB nB μ hμ]
    constructor
    · intro h hF
      apply h
      have := WeylP.fred_add_compact RB (RA - RB) hK _ hF
      rwa [add_sub_cancel] at this
    · intro h hF
      apply h
      have := WeylP.fred_add_compact RA (RB - RA) hK' _ hF
      rwa [add_sub_cancel] at this
