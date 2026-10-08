-- Prove2me | solution 1 for VectorPayoffs.Convex.blackwell_lemma
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T19:24:53.655684+00:00
-- url     : https://prove2.me/submissions/293b470e-4470-4210-b099-12e8f3d9c3d7

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Recursion

/-!
Blackwell (1956), LEMMA: a nonnegative bounded sequence `δ_n` with `|δ_n - δ_{n-1}| ≤ b / n` and
`E(δ_n | past) ≤ (1 - 2/n) δ_{n-1} + c / n²` (when `δ_{n-1} > 0`) exceeds `ε` at some time `n ≥ N₀`
with probability `< ε`, where `N₀` depends only on `a, b, c, ε`.

Proof (excursion argument).  Put `Y_n = n δ_n` with increments `D_k = Y_k - Y_{k-1}`, `|D_k| ≤ a + b`.
While `δ > ε/2` and `k ≥ N₁ ≈ 4c/ε`, `E(D_k | past) ≤ -δ_{k-1} + c/k ≤ -ε/4`.  If `δ_n ≥ ε` for some
late `n`, let `m < n` be the last time `≥ N₁` with `δ_m ≤ ε/2` (or `N₁`); then `δ_j > ε/2` on `(m, n]`
and `Y_n - Y_{m+1} ≥ nε/2 - K₀`.  For fixed `m`, the rescaled increments `D_k / (a + b)` of this
excursion (set to `0` outside it) satisfy the hypotheses of Blackwell's Theorem 2 (proved here in the
generality of an arbitrary filtration, `theorem2_gen`, via an exponential supermartingale and Ville's
inequality) with `u ≍ ε / (a + b)`, so the excursion reaches level `≍ nε` with probability `≤ r ^ n`,
`r < 1`.  A union bound over `m < n` and `n ≥ N₀` gives a tail `∑_{n ≥ N₀} n r ^ n`, which is `< ε`
for `N₀` large.  Larger `a, b, c` only weaken the hypotheses, so one may assume `a, b, c ≥ 1`.
-/

open MeasureTheory

namespace VectorPayoffs.Convex

section Thm2

variable {Ω : Type} [MeasurableSpace Ω]

/-- The natural filtration of the sequence `z₁, z₂, …`. -/
noncomputable def pastFiltration (z : ℕ → Ω → ℝ) (hmeas : ∀ k, 1 ≤ k → Measurable (z k)) :
    Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq := pastSigma z
  mono' := by
    apply monotone_nat_of_le_succ
    intro n
    unfold pastSigma
    have hg : Measurable (fun (v : Fin (n + 1) → ℝ) (i : Fin n) => v i.castSucc) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply _)
    have : (fun ω (i : Fin n) => z (i.val + 1) ω) =
        (fun (v : Fin (n + 1) → ℝ) (i : Fin n) => v i.castSucc) ∘
          (fun ω (i : Fin (n + 1)) => z (i.val + 1) ω) := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hg.comap_le
  le' := by
    intro n
    unfold pastSigma
    refine Measurable.comap_le ?_
    exact measurable_pi_iff.mpr (fun i => hmeas (i.val + 1) (by omega))

theorem exp_bound (u : ℝ) (hu : 0 < u) (hu1 : u < 1) (z : ℝ) (hz : |z| ≤ 1) :
    Real.exp (Real.log ((1 + u) / (1 - u)) * z) ≤
      1 + (2 * u / ((1 - u) * (1 + u))) * (z + u * |z|) := by
  have h1u : 0 < 1 - u := by linarith
  have h1u' : 0 < 1 + u := by linarith
  set lam := Real.log ((1 + u) / (1 - u)) with hlam
  have hexp : Real.exp lam = (1 + u) / (1 - u) := Real.exp_log (by positivity)
  have hexp' : Real.exp (-lam) = (1 - u) / (1 + u) := by
    rw [Real.exp_neg, hexp, inv_div]
  have hz' := abs_le.mp hz
  rcases le_or_gt 0 z with hz0 | hz0
  · rw [abs_of_nonneg hz0]
    have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ lam)
      (by linarith : 0 ≤ 1 - z) hz0 (by ring : (1 - z) + z = 1)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
    rw [hexp] at h
    rw [mul_comm z lam] at h
    refine h.trans (le_of_eq ?_)
    field_simp
    ring
  · rw [abs_of_neg hz0]
    have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-lam))
      (by linarith : 0 ≤ 1 + z) (by linarith : 0 ≤ -z) (by ring : (1 + z) + -z = 1)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
    rw [hexp'] at h
    have e : (-z) * -lam = lam * z := by ring
    rw [e] at h
    refine h.trans (le_of_eq ?_)
    field_simp
    ring


end Thm2

open scoped NNReal ENNReal in
/-- Ville's maximal inequality for a nonnegative supermartingale. -/
theorem ville_ineq {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℕ m0} {M : ℕ → Ω → ℝ} (hM : Supermartingale M 𝒢 μ)
    (hnn : ∀ k ω, 0 ≤ M k ω) (a : ℝ≥0) (n : ℕ) :
    a * μ {ω | (a : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => M k ω} ≤ ENNReal.ofReal (∫ ω, M 0 ω ∂μ) := by
  have hsub := hM.neg
  set τ : Ω → WithTop ℕ := fun ω => ((hittingBtwn M {y : ℝ | (a : ℝ) ≤ y} 0 n ω : ℕ) : WithTop ℕ)
    with hτdef
  have hτ : IsStoppingTime 𝒢 τ :=
    hM.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hbdd : ∀ ω, τ ω ≤ n := fun ω => by
    simp only [hτdef]
    exact_mod_cast (hittingBtwn_le (u := M) (s := {y : ℝ | (a : ℝ) ≤ y}) (n := 0) (m := n) ω)
  have hmono : ∫ ω, stoppedValue (-M) (fun _ => ((0 : ℕ) : WithTop ℕ)) ω ∂μ ≤
      ∫ ω, stoppedValue (-M) τ ω ∂μ :=
    hsub.expected_stoppedValue_mono (isStoppingTime_const 𝒢 0) hτ
      (fun ω => WithTop.coe_le_coe.mpr (Nat.zero_le _)) hbdd
  have hneg : stoppedValue (-M) τ = fun ω => -stoppedValue M τ ω := by
    ext ω; simp [stoppedValue]
  have hneg0 : stoppedValue (-M) (fun _ => ((0 : ℕ) : WithTop ℕ)) = fun ω => -M 0 ω := by
    ext ω; rfl
  rw [hneg, hneg0, integral_neg, integral_neg] at hmono
  have hint : Integrable (stoppedValue M τ) μ := by
    have := hsub.integrable_stoppedValue hτ hbdd
    rw [hneg] at this
    exact integrable_neg_iff.mp this
  have hnn' : ∀ ω, 0 ≤ stoppedValue M τ ω := fun ω => hnn _ _
  have hmeas : MeasurableSet {ω | (a : ℝ) ≤ (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one fun k => M k ω} :=
    measurableSet_le measurable_const
      (Finset.measurable_range_sup'' fun n _ => (hM.stronglyMeasurable n).measurable.le (𝒢.le n))
  have hge : ∀ ω ∈ {ω | (a : ℝ) ≤ (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one fun k => M k ω}, (a : ℝ) ≤ stoppedValue M τ ω := by
    intro ω hω
    have hω' : (a : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => M k ω := hω
    simp_rw [Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff] at hω'
    refine stoppedValue_hittingBtwn_mem ?_
    obtain ⟨j, hj₁, hj₂⟩ := hω'
    exact ⟨j, ⟨Nat.zero_le _, hj₁⟩, hj₂⟩
  have h1 := setIntegral_ge_of_const_le_real hmeas (measure_ne_top _ _) hge hint.integrableOn
  have h2 : ∫ ω in {ω | (a : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => M k ω}, stoppedValue M τ ω ∂μ ≤
      ∫ ω, stoppedValue M τ ω ∂μ :=
    setIntegral_le_integral hint (ae_of_all _ hnn')
  have h3 : (a : ℝ) * μ.real {ω | (a : ℝ) ≤ (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one fun k => M k ω} ≤ ∫ ω, M 0 ω ∂μ := by
    linarith
  calc (a : ℝ≥0∞) * μ {ω | (a : ℝ) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one fun k => M k ω}
      = ENNReal.ofReal ((a : ℝ) * μ.real {ω | (a : ℝ) ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one fun k => M k ω}) := by
        rw [ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_coe_nnreal,
          ofReal_measureReal (measure_ne_top _ _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal h3

section Thm2'

variable {Ω : Type} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem sum_Icc_eq_sum_fin (z : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.Icc 1 k, z i ω = ∑ i : Fin k, z (i.val + 1) ω := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Fin.sum_univ_castSucc]
    simp

theorem measurable_tuple_fun (z : ℕ → Ω → ℝ) (k : ℕ) (g : (Fin k → ℝ) → ℝ)
    (hg : Measurable g) :
    Measurable[pastSigma z k] (fun ω => g (fun i : Fin k => z (i.val + 1) ω)) :=
  @Measurable.comp _ _ _ (pastSigma z k) _ _ _ _ hg
    (Measurable.of_comap_le (le_refl (pastSigma z k)))

open scoped NNReal ENNReal in
theorem theorem2_gen {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (z : ℕ → Ω → ℝ) (u : ℝ) (hu : 0 < u) (hu1 : u < 1)
    (hadapt : ∀ k, 1 ≤ k → Measurable[𝒢 k] (z k))
    (hbound : ∀ k, 1 ≤ k → ∀ᵐ ω ∂μ, |z k ω| ≤ 1)
    (hdrift : ∀ k, 1 ≤ k →
      μ[z k | 𝒢 (k - 1)] ≤ᵐ[μ] (-u) • μ[fun ω => |z k ω| | 𝒢 (k - 1)])
    (t : ℝ) :
    μ {ω | ∃ k, 1 ≤ k ∧ t ≤ ∑ i ∈ Finset.Icc 1 k, z i ω} ≤
      ENNReal.ofReal (((1 - u) / (1 + u)) ^ t) := by
  classical
  have h1u : 0 < 1 - u := by linarith
  have h1u' : 0 < 1 + u := by linarith
  set ρ : ℝ := (1 - u) / (1 + u) with hρ
  have hρpos : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one h1u']; linarith
  rcases le_or_gt t 0 with ht | ht
  · calc μ {ω | ∃ k, 1 ≤ k ∧ t ≤ ∑ i ∈ Finset.Icc 1 k, z i ω} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal (ρ ^ t) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal
          (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρpos hρ1.le ht)
  set lam : ℝ := Real.log ((1 + u) / (1 - u)) with hlam
  have hr1 : 1 < (1 + u) / (1 - u) := by rw [one_lt_div h1u]; linarith
  have hlam_pos : 0 < lam := Real.log_pos hr1
  have hρexp : ρ = Real.exp (-lam) := by
    rw [Real.exp_neg, hlam, Real.exp_log (by positivity), hρ, inv_div]
  set c : ℝ := 2 * u / ((1 - u) * (1 + u)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hmeas : ∀ k, 1 ≤ k → Measurable (z k) := fun k hk => (hadapt k hk).mono (𝒢.le k) le_rfl
  let S : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ Finset.Icc 1 k, z i ω
  let M : ℕ → Ω → ℝ := fun k ω => Real.exp (lam * S k ω)
  have hSmeas : ∀ k, Measurable (S k) := fun k =>
    Finset.measurable_sum _ (fun i hi => hmeas i (Finset.mem_Icc.mp hi).1)
  have hSbound : ∀ k, ∀ᵐ ω ∂μ, |S k ω| ≤ k := by
    intro k
    induction k with
    | zero => exact ae_of_all _ (fun ω => by simp [S])
    | succ k ih =>
      filter_upwards [ih, hbound (k + 1) (by omega)] with ω h1 h2
      have : S (k + 1) ω = S k ω + z (k + 1) ω := by
        simp only [S]; rw [Finset.sum_Icc_succ_top (by omega)]
      rw [this]
      calc |S k ω + z (k + 1) ω| ≤ |S k ω| + |z (k + 1) ω| := abs_add_le _ _
        _ ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hMmeas : ∀ k, Measurable (M k) := fun k =>
    Real.measurable_exp.comp ((hSmeas k).const_mul lam)
  have hMint : ∀ k, Integrable (M k) μ := by
    intro k
    refine Integrable.of_bound (hMmeas k).aestronglyMeasurable (Real.exp (lam * k)) ?_
    filter_upwards [hSbound k] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp hω).2])
  have hMadp : StronglyAdapted 𝒢 M := by
    intro k
    have hS : Measurable[𝒢 k] (S k) :=
      Finset.measurable_sum _ (fun i hi => by
        have hi' := Finset.mem_Icc.mp hi
        exact (hadapt i hi'.1).mono (𝒢.mono hi'.2) le_rfl)
    exact (Real.measurable_exp.comp (hS.const_mul lam)).stronglyMeasurable
  have hzint : ∀ k, 1 ≤ k → Integrable (z k) μ := fun k hk =>
    Integrable.of_bound (hmeas k hk).aestronglyMeasurable 1 (by
      filter_upwards [hbound k hk] with ω hω
      rwa [Real.norm_eq_abs])
  have habsint : ∀ k, 1 ≤ k → Integrable (fun ω => |z k ω|) μ := fun k hk => (hzint k hk).abs
  have hstep : ∀ k, μ[M (k + 1) | 𝒢 k] ≤ᵐ[μ] M k := by
    intro k
    have hk1 : 1 ≤ k + 1 := by omega
    set W : Ω → ℝ := fun ω => Real.exp (lam * z (k + 1) ω) with hW
    have hWmeas : Measurable W := Real.measurable_exp.comp ((hmeas _ hk1).const_mul lam)
    have hWint : Integrable W μ := by
      refine Integrable.of_bound hWmeas.aestronglyMeasurable (Real.exp lam) ?_
      filter_upwards [hbound (k + 1) hk1] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp hω).2])
    have hprod : M (k + 1) = M k * W := by
      ext ω
      simp only [M, S, W, Pi.mul_apply]
      rw [Finset.sum_Icc_succ_top (by omega), mul_add, Real.exp_add]
    have hMk_sm : StronglyMeasurable[𝒢 k] (M k) := hMadp k
    have hpull := condExp_mul_of_stronglyMeasurable_left hMk_sm (hprod ▸ hMint (k + 1))
      hWint (m := 𝒢 k)
    set g : Ω → ℝ := fun ω => 1 + c * (z (k + 1) ω + u * |z (k + 1) ω|) with hg
    have hgint : Integrable g μ :=
      (integrable_const (1 : ℝ)).add (((hzint _ hk1).add ((habsint _ hk1).const_mul u)).const_mul c)
    have hle : W ≤ᵐ[μ] g := by
      filter_upwards [hbound (k + 1) hk1] with ω hω
      exact exp_bound u hu hu1 _ hω
    have hcm := condExp_mono (m := 𝒢 k) hWint hgint hle
    have hg_eq : μ[g | 𝒢 k] =ᵐ[μ] fun ω => 1 + c * (μ[z (k + 1) | 𝒢 k] ω +
        u * μ[fun ω => |z (k + 1) ω| | 𝒢 k] ω) := by
      have e : g = (fun _ => (1 : ℝ)) + c • (z (k + 1) + u • fun ω => |z (k + 1) ω|) := by
        ext ω; simp [g]; ring
      rw [e]
      have i1 := hzint _ hk1
      have i2 := habsint _ hk1
      have c1 := condExp_add (μ := μ) (integrable_const (1 : ℝ))
        ((i1.add (i2.smul u)).smul c) (𝒢 k)
      have c2 := condExp_smul (μ := μ) c (z (k + 1) + u • fun ω => |z (k + 1) ω|) (𝒢 k)
      have c3 := condExp_add (μ := μ) i1 (i2.smul u) (𝒢 k)
      have c4 := condExp_smul (μ := μ) u (fun ω => |z (k + 1) ω|) (𝒢 k)
      have c5 := condExp_const (μ := μ) (𝒢.le k) (1 : ℝ)
      filter_upwards [c1, c2, c3, c4] with ω h1 h2 h3 h4
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4 ⊢
      rw [h1, h2, h3, h4, c5]
    have hd := hdrift (k + 1) hk1
    simp only [Nat.add_sub_cancel] at hd
    filter_upwards [hpull, hcm, hg_eq, hd] with ω h1 h2 h3 h4
    have h4' : μ[z (k + 1) | 𝒢 k] ω ≤ -u * μ[fun ω => |z (k + 1) ω| | 𝒢 k] ω := by
      simpa using h4
    have h5 : μ[W | 𝒢 k] ω ≤ 1 := by
      have : μ[z (k + 1) | 𝒢 k] ω ≤ -u * μ[fun ω => |z (k + 1) ω| | 𝒢 k] ω := h4'
      have h6 : c * (μ[z (k + 1) | 𝒢 k] ω + u * μ[fun ω => |z (k + 1) ω| | 𝒢 k] ω) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc0 (by linarith)
      linarith
    have hMpos : 0 ≤ M k ω := (Real.exp_pos _).le
    rw [hprod, h1]
    show M k ω * μ[W | 𝒢 k] ω ≤ M k ω
    nlinarith
  have hsuper : Supermartingale M 𝒢 μ := supermartingale_nat hMadp hMint hstep
  have hnn : ∀ k ω, 0 ≤ M k ω := fun k ω => (Real.exp_pos _).le
  have hM0 : ∫ ω, M 0 ω ∂μ = 1 := by simp [M, S]
  let A : ℝ≥0 := ⟨Real.exp (lam * t), (Real.exp_pos _).le⟩
  have hApos : 0 < (A : ℝ) := Real.exp_pos _
  have hA0 : (A : ℝ≥0∞) ≠ 0 := by
    simpa using (show A ≠ 0 from fun h => by simpa [h] using hApos)
  have hρt : ρ ^ t = (A : ℝ)⁻¹ := by
    rw [Real.rpow_def_of_pos hρpos, hρexp, Real.log_exp]
    show Real.exp (-lam * t) = (Real.exp (lam * t))⁻¹
    rw [← Real.exp_neg]; congr 1; ring
  have hfin : ∀ n, μ {ω | ∃ k, 1 ≤ k ∧ k ≤ n ∧ t ≤ S k ω} ≤ ENNReal.ofReal (ρ ^ t) := by
    intro n
    have hv := ville_ineq hsuper hnn A n
    rw [hM0, ENNReal.ofReal_one] at hv
    have hsub : {ω | ∃ k, 1 ≤ k ∧ k ≤ n ∧ t ≤ S k ω} ⊆ {ω | (A : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => M k ω} := by
      rintro ω ⟨k, hk1, hkn, hkt⟩
      show (A : ℝ) ≤ _
      refine le_trans ?_ (Finset.le_sup' (fun k => M k ω) (Finset.mem_range.mpr (by omega : k < n + 1)))
      exact Real.exp_le_exp.mpr (by nlinarith)
    have h1 : (A : ℝ≥0∞) * μ {ω | ∃ k, 1 ≤ k ∧ k ≤ n ∧ t ≤ S k ω} ≤ 1 :=
      (mul_le_mul' le_rfl (measure_mono hsub)).trans hv
    rw [hρt, ENNReal.ofReal_inv_of_pos hApos, ENNReal.ofReal_coe_nnreal]
    rw [ENNReal.mul_le_iff_le_inv hA0 ENNReal.coe_ne_top] at h1
    simpa using h1
  have hunion : {ω | ∃ k, 1 ≤ k ∧ t ≤ ∑ i ∈ Finset.Icc 1 k, z i ω} =
      ⋃ n : ℕ, {ω | ∃ k, 1 ≤ k ∧ k ≤ n ∧ t ≤ S k ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk, hkt⟩; exact ⟨k, k, hk, le_rfl, hkt⟩
    · rintro ⟨n, k, hk, _, hkt⟩; exact ⟨k, hk, hkt⟩
  rw [hunion, Monotone.measure_iUnion]
  · exact iSup_le hfin
  · intro n m hnm ω ⟨k, hk, hkn, hkt⟩
    exact ⟨k, hk, hkn.trans hnm, hkt⟩


theorem measurable_past_self (δ : ℕ → Ω → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Measurable[pastSigma δ n] (δ n) := by
  have h := measurable_tuple_fun δ n (fun v => v ⟨n - 1, by omega⟩) (measurable_pi_apply _)
  convert h using 1
  funext ω
  simp [Nat.sub_add_cancel hn]

theorem satisfiesRecursion_mono {a b c a' b' c' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    {μ : Measure Ω} {δ : ℕ → Ω → ℝ} (h : SatisfiesRecursion a b c μ δ) :
    SatisfiesRecursion a' b' c' μ δ := by
  obtain ⟨h5, h6, h7⟩ := h
  refine ⟨fun n hn => ?_, fun n hn => ?_, fun n hn => ?_⟩
  · filter_upwards [h5 n hn] with ω hω hpos
    have := hω hpos
    have h2 : c / (n : ℝ) ^ 2 ≤ c' / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hc (sq_nonneg _)
    linarith
  · filter_upwards [h6 n hn] with ω hω
    exact ⟨hω.1, hω.2.trans ha⟩
  · filter_upwards [h7 n hn] with ω hω
    exact hω.trans (div_le_div_of_nonneg_right hb (Nat.cast_nonneg _))

/-- The increments `Y_k - Y_{k-1}` of `Y_n = n δ_n`. -/
noncomputable def incr (δ : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  (k : ℝ) * δ k ω - ((k - 1 : ℕ) : ℝ) * δ (k - 1) ω

/-- The event that `δ_j > ε/2` for all `m < j < k` (empty unless `m + 2 ≤ k`). -/
def excursionSet (δ : ℕ → Ω → ℝ) (ε : ℝ) (m k : ℕ) : Set Ω :=
  if m + 2 ≤ k then ⋂ j ∈ Finset.Ioo m k, {ω | ε / 2 < δ j ω} else ∅

/-- Rescaled increments of `n δ_n` during an excursion above `ε/2` started at time `m`. -/
noncomputable def zz (δ : ℕ → Ω → ℝ) (ε B : ℝ) (m k : ℕ) : Ω → ℝ :=
  (excursionSet δ ε m k).indicator (fun ω => incr δ k ω / B)

theorem mem_excursionSet {δ : ℕ → Ω → ℝ} {ε : ℝ} {m k : ℕ} {ω : Ω} :
    ω ∈ excursionSet δ ε m k ↔ m + 2 ≤ k ∧ ∀ j, m < j → j < k → ε / 2 < δ j ω := by
  unfold excursionSet
  split_ifs with h
  · simp only [Set.mem_iInter, Finset.mem_Ioo, Set.mem_setOf_eq]
    constructor
    · intro hω; exact ⟨h, fun j h1 h2 => hω j ⟨h1, h2⟩⟩
    · intro hω j hj; exact hω.2 j hj.1 hj.2
  · simp [h]

theorem excursionSet_meas {δ : ℕ → Ω → ℝ} (hδm : ∀ n, 1 ≤ n → Measurable (δ n)) {ε : ℝ} {m k : ℕ}
    (hkm : m + 2 ≤ k) :
    MeasurableSet[pastSigma δ (k - 1)] (excursionSet δ ε m k) := by
  unfold excursionSet
  rw [if_pos hkm]
  refine Finset.measurableSet_biInter _ (fun j hj => ?_)
  have hj' := Finset.mem_Ioo.mp hj
  have h1 : Measurable[pastSigma δ j] (δ j) := measurable_past_self δ j (by omega)
  have h2 : pastSigma δ j ≤ pastSigma δ (k - 1) := (pastFiltration δ hδm).mono (by omega)
  exact measurableSet_lt measurable_const (h1.mono h2 le_rfl)

theorem ae_bounds {μ : Measure Ω} {δ : ℕ → Ω → ℝ} {a b c : ℝ}
    (hrec : SatisfiesRecursion a b c μ δ) :
    ∀ᵐ ω ∂μ, (∀ n, 1 ≤ n → 0 ≤ δ n ω ∧ δ n ω ≤ a) ∧
      (∀ n, 2 ≤ n → |δ n ω - δ (n - 1) ω| ≤ b / n) := by
  obtain ⟨_, h6, h7⟩ := hrec
  have e1 : ∀ᵐ ω ∂μ, ∀ n, 1 ≤ n → 0 ≤ δ n ω ∧ δ n ω ≤ a := by
    rw [ae_all_iff]
    intro n
    by_cases hn : 1 ≤ n
    · filter_upwards [h6 n hn] with ω hω _ using hω
    · exact ae_of_all _ (fun ω h => absurd h hn)
  have e2 : ∀ᵐ ω ∂μ, ∀ n, 2 ≤ n → |δ n ω - δ (n - 1) ω| ≤ b / n := by
    rw [ae_all_iff]
    intro n
    by_cases hn : 2 ≤ n
    · filter_upwards [h7 n hn] with ω hω _ using hω
    · exact ae_of_all _ (fun ω h => absurd h hn)
  filter_upwards [e1, e2] with ω h1 h2 using ⟨h1, h2⟩

theorem incr_eq (δ : ℕ → Ω → ℝ) {k : ℕ} (hk : 1 ≤ k) (ω : Ω) :
    incr δ k ω = (k : ℝ) * (δ k ω - δ (k - 1) ω) + δ (k - 1) ω := by
  unfold incr
  rw [Nat.cast_sub hk]
  push_cast
  ring

theorem incr_bound {δ : ℕ → Ω → ℝ} {ω : Ω} {a b : ℝ}
    (h1 : ∀ n, 1 ≤ n → 0 ≤ δ n ω ∧ δ n ω ≤ a)
    (h2 : ∀ n, 2 ≤ n → |δ n ω - δ (n - 1) ω| ≤ b / n) {k : ℕ} (hk : 2 ≤ k) :
    |incr δ k ω| ≤ a + b := by
  rw [incr_eq δ (by omega)]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have h3 := h2 k hk
  have h4 := h1 (k - 1) (by omega)
  have h5 : (k : ℝ) * |δ k ω - δ (k - 1) ω| ≤ b := by
    calc (k : ℝ) * |δ k ω - δ (k - 1) ω| ≤ (k : ℝ) * (b / k) :=
          mul_le_mul_of_nonneg_left h3 hk0.le
      _ = b := by field_simp
  calc |(k : ℝ) * (δ k ω - δ (k - 1) ω) + δ (k - 1) ω|
      ≤ |(k : ℝ) * (δ k ω - δ (k - 1) ω)| + |δ (k - 1) ω| := abs_add_le _ _
    _ = (k : ℝ) * |δ k ω - δ (k - 1) ω| + |δ (k - 1) ω| := by
        rw [abs_mul, abs_of_pos hk0]
    _ ≤ b + a := by rw [abs_of_nonneg h4.1]; linarith [h4.2]
    _ = a + b := by ring

theorem zz_adapted {δ : ℕ → Ω → ℝ} (hδm : ∀ n, 1 ≤ n → Measurable (δ n)) (ε B : ℝ) (m k : ℕ)
    (hk : 1 ≤ k) : Measurable[pastSigma δ k] (zz δ ε B m k) := by
  by_cases hkm : m + 2 ≤ k
  · have hA : MeasurableSet[pastSigma δ k] (excursionSet δ ε m k) :=
      (pastFiltration δ hδm).mono (by omega : k - 1 ≤ k) _ (excursionSet_meas hδm hkm)
    have h1 : Measurable[pastSigma δ k] (δ k) := measurable_past_self δ k hk
    have h2 : Measurable[pastSigma δ k] (δ (k - 1)) :=
      (measurable_past_self δ (k - 1) (by omega)).mono
        ((pastFiltration δ hδm).mono (by omega : k - 1 ≤ k)) le_rfl
    refine Measurable.indicator ?_ hA
    unfold incr
    exact ((h1.const_mul _).sub (h2.const_mul _)).div_const B
  · have : zz δ ε B m k = fun _ => 0 := by
      ext ω
      simp [zz, excursionSet, hkm]
    rw [this]
    exact measurable_const

theorem zz_bound {μ : Measure Ω} {δ : ℕ → Ω → ℝ} {a b c : ℝ} (hrec : SatisfiesRecursion a b c μ δ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (ε : ℝ) (m k : ℕ) :
    ∀ᵐ ω ∂μ, |zz δ ε (a + b) m k ω| ≤ 1 := by
  filter_upwards [ae_bounds hrec] with ω ⟨h1, h2⟩
  have hB : 0 < a + b := by linarith
  by_cases hω : ω ∈ excursionSet δ ε m k
  · have hk := (mem_excursionSet.mp hω).1
    have := incr_bound h1 h2 (by omega : 2 ≤ k)
    simp only [zz, Set.indicator_of_mem hω]
    rw [abs_div, abs_of_pos hB, div_le_one hB]
    exact this
  · simp [zz, Set.indicator_of_notMem hω]

theorem delta_integrable {μ : Measure Ω} [IsProbabilityMeasure μ] {δ : ℕ → Ω → ℝ} {a b c : ℝ}
    (hδm : ∀ n, 1 ≤ n → Measurable (δ n)) (hrec : SatisfiesRecursion a b c μ δ) {n : ℕ}
    (hn : 1 ≤ n) : Integrable (δ n) μ := by
  refine Integrable.of_bound (hδm n hn).aestronglyMeasurable a ?_
  filter_upwards [hrec.2.1 n hn] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
  exact hω.2

theorem incr_integrable {μ : Measure Ω} [IsProbabilityMeasure μ] {δ : ℕ → Ω → ℝ} {a b c : ℝ}
    (hδm : ∀ n, 1 ≤ n → Measurable (δ n)) (hrec : SatisfiesRecursion a b c μ δ) {k : ℕ}
    (hk : 2 ≤ k) : Integrable (incr δ k) μ := by
  have h1 := delta_integrable hδm hrec (by omega : 1 ≤ k)
  have h2 := delta_integrable hδm hrec (by omega : 1 ≤ k - 1)
  unfold incr
  exact (h1.const_mul _).sub (h2.const_mul _)

theorem zz_drift {μ : Measure Ω} [IsProbabilityMeasure μ] {δ : ℕ → Ω → ℝ} {a b c : ℝ}
    (hδm : ∀ n, 1 ≤ n → Measurable (δ n)) (hrec : SatisfiesRecursion a b c μ δ)
    {ε : ℝ} (hε : 0 < ε) (ha : 1 ≤ a) (hb : 1 ≤ b) {u : ℝ} (hu0 : 0 < u)
    (hu : u ≤ ε / (4 * (a + b))) {m : ℕ} (hm : 4 * c / ε ≤ m) (k : ℕ) (hk : 1 ≤ k) :
    μ[zz δ ε (a + b) m k | pastSigma δ (k - 1)] ≤ᵐ[μ]
      (-u) • μ[fun ω => |zz δ ε (a + b) m k ω| | pastSigma δ (k - 1)] := by
  classical
  have hrec' := hrec
  obtain ⟨h5, h6, h7⟩ := hrec
  set B : ℝ := a + b with hB
  have hBpos : 0 < B := by linarith
  by_cases hkm : m + 2 ≤ k
  swap
  · have h0 : zz δ ε B m k = 0 := by
      ext ω
      simp [zz, excursionSet, hkm]
    have h0' : (fun ω => |zz δ ε B m k ω|) = 0 := by
      ext ω
      simp [h0]
    rw [h0', h0, condExp_zero]
    simp only [smul_zero]
    exact Filter.EventuallyLE.refl _ _
  have hFle : pastSigma δ (k - 1) ≤ (inferInstance : MeasurableSpace Ω) := (pastFiltration δ hδm).le (k - 1)
  have hk2 : 2 ≤ k := by omega
  have hA : MeasurableSet[pastSigma δ (k - 1)] (excursionSet δ ε m k) := excursionSet_meas hδm hkm
  have hI := incr_integrable hδm hrec' hk2
  have hf1 : Integrable (fun ω => incr δ k ω / B) μ := hI.div_const B
  have hf2 : Integrable (fun ω => |incr δ k ω| / B) μ := hI.abs.div_const B
  have hind1 := condExp_indicator (m := pastSigma δ (k - 1)) hf1 hA
  have hind2 := condExp_indicator (m := pastSigma δ (k - 1)) hf2 hA
  have habs : (fun ω => |zz δ ε B m k ω|) =
      (excursionSet δ ε m k).indicator (fun ω => |incr δ k ω| / B) := by
    ext ω
    by_cases h : ω ∈ excursionSet δ ε m k
    · simp [zz, Set.indicator_of_mem h, abs_div, abs_of_pos hBpos]
    · simp [zz, Set.indicator_of_notMem h]
  rw [habs]
  have hz : zz δ ε B m k = (excursionSet δ ε m k).indicator (fun ω => incr δ k ω / B) := rfl
  rw [hz]
  -- conditional expectation of the increment
  have hδk := delta_integrable hδm hrec' (by omega : 1 ≤ k)
  have hδk1 := delta_integrable hδm hrec' (by omega : 1 ≤ k - 1)
  have hsm : StronglyMeasurable[pastSigma δ (k - 1)] (δ (k - 1)) :=
    (measurable_past_self δ (k - 1) (by omega)).stronglyMeasurable
  have hE1 : μ[fun ω => incr δ k ω / B | pastSigma δ (k - 1)] =ᵐ[μ] fun ω =>
      B⁻¹ * ((k : ℝ) * μ[δ k | pastSigma δ (k - 1)] ω - ((k - 1 : ℕ) : ℝ) * δ (k - 1) ω) := by
    have e : (fun ω => incr δ k ω / B) =
        B⁻¹ • (((k : ℝ) • δ k) - (((k - 1 : ℕ) : ℝ) • δ (k - 1))) := by
      ext ω
      simp [incr, div_eq_inv_mul]
    rw [e]
    have c1 := condExp_smul (μ := μ) B⁻¹ (((k : ℝ) • δ k) - (((k - 1 : ℕ) : ℝ) • δ (k - 1))) (pastSigma δ (k - 1))
    have c2 := condExp_sub (μ := μ) (hδk.smul (k : ℝ)) (hδk1.smul ((k - 1 : ℕ) : ℝ)) (pastSigma δ (k - 1))
    have c3 := condExp_smul (μ := μ) (k : ℝ) (δ k) (pastSigma δ (k - 1))
    have c4 := condExp_smul (μ := μ) ((k - 1 : ℕ) : ℝ) (δ (k - 1)) (pastSigma δ (k - 1))
    have c5 := condExp_of_stronglyMeasurable hFle hsm hδk1
    filter_upwards [c1, c2, c3, c4] with ω h1 h2 h3 h4
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1 h2 h3 h4 ⊢
    rw [h1, h2, h3, h4, c5]
  have hbd : μ[fun ω => |incr δ k ω| / B | pastSigma δ (k - 1)] ≤ᵐ[μ] fun _ => 1 := by
    have hle : (fun ω => |incr δ k ω| / B) ≤ᵐ[μ] fun _ => (1 : ℝ) := by
      filter_upwards [ae_bounds hrec'] with ω ⟨h1', h2'⟩
      have := incr_bound h1' h2' hk2
      show |incr δ k ω| / B ≤ 1
      rw [div_le_one hBpos]; exact this
    have := condExp_mono (m := pastSigma δ (k - 1)) hf2 (integrable_const (1 : ℝ)) hle
    rwa [condExp_const hFle] at this
  have hrec5 := h5 k hk2
  filter_upwards [hind1, hind2, hE1, hrec5, hbd] with ω i1 i2 e1 r5 b2
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [i1, i2]
  by_cases hω : ω ∈ excursionSet δ ε m k
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, e1]
    obtain ⟨_, hjω⟩ := mem_excursionSet.mp hω
    have hd : ε / 2 < δ (k - 1) ω := hjω (k - 1) (by omega) (by omega)
    have hd0 : 0 < δ (k - 1) ω := by linarith
    have hX := r5 hd0
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hck : c / (k : ℝ) ≤ ε / 4 := by
      rw [div_le_iff₀ hk0]
      have h1 : 4 * c / ε ≤ (k : ℝ) := by
        have : (m : ℝ) ≤ k := by exact_mod_cast (by omega : m ≤ k)
        linarith
      rw [div_le_iff₀ hε] at h1
      linarith
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have hkX : (k : ℝ) * μ[δ k | pastSigma δ (k - 1)] ω ≤ ((k : ℝ) - 2) * δ (k - 1) ω + c / k := by
      have h1 : (k : ℝ) * μ[δ k | pastSigma δ (k - 1)] ω ≤
          (k : ℝ) * ((1 - 2 / (k : ℝ)) * δ (k - 1) ω + c / (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hX hk0.le
      have h2 : (k : ℝ) * ((1 - 2 / (k : ℝ)) * δ (k - 1) ω + c / (k : ℝ) ^ 2) =
          ((k : ℝ) - 2) * δ (k - 1) ω + c / k := by
        field_simp
      linarith
    have hinner : (k : ℝ) * μ[δ k | pastSigma δ (k - 1)] ω - ((k - 1 : ℕ) : ℝ) * δ (k - 1) ω ≤ -(ε / 4) := by
      rw [hcast]
      nlinarith
    have hu' : u ≤ ε / (4 * B) := hu
    have hεB : ε / (4 * B) = (ε / 4) / B := by field_simp
    calc B⁻¹ * ((k : ℝ) * μ[δ k | pastSigma δ (k - 1)] ω - ((k - 1 : ℕ) : ℝ) * δ (k - 1) ω)
        ≤ B⁻¹ * (-(ε / 4)) := mul_le_mul_of_nonneg_left hinner (inv_nonneg.mpr hBpos.le)
      _ = -((ε / 4) / B) := by field_simp
      _ ≤ -u := by rw [← hεB]; linarith
      _ ≤ -u * μ[fun ω => |incr δ k ω| / B | pastSigma δ (k - 1)] ω := by nlinarith
  · simp [Set.indicator_of_notMem hω]

theorem incr_tele (δ : ℕ → Ω → ℝ) (ω : Ω) (m : ℕ) :
    ∀ n, m + 1 ≤ n → ∑ i ∈ Finset.Icc (m + 2) n, incr δ i ω =
      (n : ℝ) * δ n ω - ((m + 1 : ℕ) : ℝ) * δ (m + 1) ω := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    unfold incr
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

theorem zz_sum {δ : ℕ → Ω → ℝ} {ε B : ℝ} {ω : Ω} {m n : ℕ} (hmn : m + 1 ≤ n)
    (hmid : ∀ j, m < j → j ≤ n → ε / 2 < δ j ω) :
    ∑ i ∈ Finset.Icc 1 n, zz δ ε B m i ω =
      ((n : ℝ) * δ n ω - ((m + 1 : ℕ) : ℝ) * δ (m + 1) ω) / B := by
  have h1 : ∀ i ∈ Finset.Icc 1 n, zz δ ε B m i ω =
      if m + 2 ≤ i then incr δ i ω / B else 0 := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    by_cases h : m + 2 ≤ i
    · have hω : ω ∈ excursionSet δ ε m i :=
        mem_excursionSet.mpr ⟨h, fun j h1 h2 => hmid j h1 (by omega)⟩
      simp [zz, Set.indicator_of_mem hω, h]
    · have : excursionSet δ ε m i = ∅ := by
        unfold excursionSet; rw [if_neg h]
      simp [zz, this, h]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  have h2 : (Finset.Icc 1 n).filter (fun i => m + 2 ≤ i) = Finset.Icc (m + 2) n := by
    ext i; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [h2, ← Finset.sum_div, incr_tele δ ω m n hmn]

/-- The deterministic core of the excursion argument. -/
theorem pointwise_exc {δ : ℕ → Ω → ℝ} {ω : Ω} {a b ε : ℝ} (hε : 0 < ε) (ha : 1 ≤ a) (hb : 1 ≤ b)
    {N1 n : ℕ} (h1 : ∀ n, 1 ≤ n → 0 ≤ δ n ω ∧ δ n ω ≤ a)
    (h2 : ∀ n, 2 ≤ n → |δ n ω - δ (n - 1) ω| ≤ b / n) (hN1 : 1 ≤ N1)
    (hn : N1 + 1 ≤ n) (hδn : ε ≤ δ n ω) :
    ∃ m, N1 ≤ m ∧ m < n ∧
      (n * ε / 2 - (((N1 : ℝ) + 1) * a + b)) / (a + b) ≤
        ∑ i ∈ Finset.Icc 1 n, zz δ ε (a + b) m i ω := by
  classical
  have hB : 0 < a + b := by linarith
  -- the last time before `n` (and after `N1`) at which `δ ≤ ε / 2`
  have key : ∃ m, N1 ≤ m ∧ m + 1 ≤ n ∧ (∀ j, m < j → j ≤ n → ε / 2 < δ j ω) ∧
      ((m + 1 : ℕ) : ℝ) * δ (m + 1) ω ≤ ((m + 1 : ℕ) : ℝ) * (ε / 2) + (((N1 : ℝ) + 1) * a + b) := by
    by_cases hex : ∃ j, N1 ≤ j ∧ j ≤ n - 1 ∧ δ j ω ≤ ε / 2
    · obtain ⟨j0, hj0a, hj0b, hj0c⟩ := hex
      set P : ℕ → Prop := fun j => N1 ≤ j ∧ δ j ω ≤ ε / 2 with hP
      have hPj0 : P j0 := ⟨hj0a, hj0c⟩
      have hspec := Nat.findGreatest_spec (P := P) (n := n - 1) hj0b hPj0
      have hle := Nat.findGreatest_le (P := P) (n - 1)
      set m := Nat.findGreatest P (n - 1) with hm
      refine ⟨m, hspec.1, by omega, ?_, ?_⟩
      · intro j hj1 hj2
        by_cases hjn : j = n
        · subst hjn; linarith
        · have hjle : j ≤ n - 1 := by omega
          have hnot := Nat.findGreatest_is_greatest (P := P) (by omega : m < j) hjle
          have : ¬ δ j ω ≤ ε / 2 := fun h => hnot ⟨by have := hspec.1; omega, h⟩
          linarith
      · have hmN : N1 ≤ m := hspec.1
        have hm1 : 1 ≤ m + 1 := by omega
        have hm2 : 2 ≤ m + 1 := by omega
        have h7 := h2 (m + 1) hm2
        simp only [Nat.add_sub_cancel] at h7
        have hdm : δ (m + 1) ω ≤ δ m ω + b / ((m + 1 : ℕ) : ℝ) := by
          have := (abs_le.mp h7).2
          push_cast at this ⊢
          linarith
        have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
        have hm_le : δ m ω ≤ ε / 2 := hspec.2
        calc ((m + 1 : ℕ) : ℝ) * δ (m + 1) ω
            ≤ ((m + 1 : ℕ) : ℝ) * (ε / 2 + b / ((m + 1 : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left (by linarith) hpos.le
          _ = ((m + 1 : ℕ) : ℝ) * (ε / 2) + b := by field_simp
          _ ≤ ((m + 1 : ℕ) : ℝ) * (ε / 2) + (((N1 : ℝ) + 1) * a + b) := by
              have : 0 ≤ ((N1 : ℝ) + 1) * a := by positivity
              linarith
    · push Not at hex
      refine ⟨N1, le_rfl, hn, ?_, ?_⟩
      · intro j hj1 hj2
        by_cases hjn : j = n
        · subst hjn; linarith
        · have := hex j hj1.le (by omega)
          linarith
      · have h3 := (h1 (N1 + 1) (by omega)).2
        have h0 := (h1 (N1 + 1) (by omega)).1
        push_cast
        have : 0 ≤ ((N1 : ℝ) + 1) * (ε / 2) := by positivity
        nlinarith
  obtain ⟨m, hm1, hm2, hmid, hY⟩ := key
  refine ⟨m, hm1, by omega, ?_⟩
  rw [zz_sum hm2 hmid]
  apply div_le_div_of_nonneg_right _ hB.le
  have hnm : ((m + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hm2
  have hnε : (n : ℝ) * ε ≤ (n : ℝ) * δ n ω := mul_le_mul_of_nonneg_left hδn (Nat.cast_nonneg _)
  have hmε : ((m + 1 : ℕ) : ℝ) * (ε / 2) ≤ (n : ℝ) * (ε / 2) :=
    mul_le_mul_of_nonneg_right hnm (by positivity)
  nlinarith

open scoped ENNReal in
theorem lemma_core (a b c ε : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (δ : ℕ → Ω → ℝ), (∀ n, 1 ≤ n → Measurable (δ n)) → SatisfiesRecursion a b c μ δ →
        (μ {ω | ∃ n, N₀ ≤ n ∧ 1 ≤ n ∧ ε ≤ δ n ω}).toReal < ε := by
  classical
  set B : ℝ := a + b with hB
  have hBpos : 0 < B := by linarith
  set u : ℝ := min (ε / (4 * B)) (1 / 2) with hu
  have hu0 : 0 < u := lt_min (by positivity) (by norm_num)
  have hu1 : u < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have huε : u ≤ ε / (4 * B) := min_le_left _ _
  set N1 : ℕ := ⌈4 * c / ε⌉₊ + 1 with hN1
  set K0 : ℝ := ((N1 : ℝ) + 1) * a + b with hK0
  set N2 : ℕ := ⌈4 * K0 / ε⌉₊ + 1 with hN2
  set lam : ℝ := Real.log ((1 + u) / (1 - u)) with hlam
  have h1u : 0 < 1 - u := by linarith
  have h1u' : 0 < 1 + u := by linarith
  have hlam_pos : 0 < lam := Real.log_pos (by rw [one_lt_div h1u]; linarith)
  set κ : ℝ := lam * (ε / (4 * B)) with hκ
  have hκpos : 0 < κ := by positivity
  set r : ℝ := Real.exp (-κ) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [hr, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  set f : ℕ → ℝ := fun n => (n : ℝ) * r ^ n with hf
  have hfsum : Summable f := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
      (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
    simpa [hf] using this
  have hfnn : ∀ n, 0 ≤ f n := fun n => by positivity
  obtain ⟨N3, hN3⟩ : ∃ N3 : ℕ, ∀ i ≥ N3, ∑' k, f (k + i) < ε / 2 :=
    Filter.eventually_atTop.mp
      ((_root_.tendsto_sum_nat_add f).eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2)))
  set N0 : ℕ := max N2 (max (N1 + 1) N3) with hN0
  refine ⟨N0, ?_⟩
  intro Ω _ μ _ δ hδm hrec
  -- the rescaled increment sequences satisfy the hypotheses of Theorem 2
  have hz : ∀ m, N1 ≤ m → ∀ t : ℝ,
      μ {ω | ∃ k, 1 ≤ k ∧ t ≤ ∑ i ∈ Finset.Icc 1 k, zz δ ε B m i ω} ≤
        ENNReal.ofReal (((1 - u) / (1 + u)) ^ t) := by
    intro m hm t
    have hm' : 4 * c / ε ≤ m := by
      have h1 : 4 * c / ε ≤ (⌈4 * c / ε⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (N1 : ℝ) ≤ m := by exact_mod_cast hm
      have h3 : (N1 : ℝ) = (⌈4 * c / ε⌉₊ : ℝ) + 1 := by rw [hN1]; push_cast; ring
      linarith
    exact theorem2_gen μ (pastFiltration δ hδm) (zz δ ε B m) u hu0 hu1
      (fun k hk => zz_adapted hδm ε B m k hk)
      (fun k _ => zz_bound hrec ha hb ε m k)
      (fun k hk => zz_drift hδm hrec hε ha hb hu0 huε hm' k hk) t
  -- the bound for a fixed `(n, m)`
  have hbd : ∀ n m, N2 ≤ n → N1 ≤ m →
      μ {ω | ∃ k, 1 ≤ k ∧ ((n : ℝ) * ε / 2 - K0) / B ≤ ∑ i ∈ Finset.Icc 1 k, zz δ ε B m i ω}
        ≤ ENNReal.ofReal (r ^ n) := by
    intro n m hn hm
    refine (hz m hm _).trans (ENNReal.ofReal_le_ofReal ?_)
    have hn' : (n : ℝ) * ε / 4 ≥ K0 := by
      have h1 : 4 * K0 / ε ≤ (⌈4 * K0 / ε⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈4 * K0 / ε⌉₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn
      rw [div_le_iff₀ hε] at h1
      nlinarith
    have hρpos : 0 < (1 - u) / (1 + u) := by positivity
    have hρ1 : (1 - u) / (1 + u) ≤ 1 := by rw [div_le_one h1u']; linarith
    have hρexp : (1 - u) / (1 + u) = Real.exp (-lam) := by
      rw [Real.exp_neg, hlam, Real.exp_log (by positivity), inv_div]
    have h3 : (n : ℝ) * ε / (4 * B) ≤ ((n : ℝ) * ε / 2 - K0) / B := by
      rw [show (4 : ℝ) * B = 4 * B from rfl, div_le_div_iff₀ (by positivity) hBpos]
      nlinarith
    calc ((1 - u) / (1 + u)) ^ (((n : ℝ) * ε / 2 - K0) / B)
        ≤ ((1 - u) / (1 + u)) ^ ((n : ℝ) * ε / (4 * B)) :=
          Real.rpow_le_rpow_of_exponent_ge hρpos hρ1 h3
      _ = r ^ n := by
          rw [Real.rpow_def_of_pos hρpos, hρexp, Real.log_exp, hr, ← Real.exp_nat_mul]
          congr 1
          rw [hκ]; field_simp
  -- almost surely, a late exceedance lies in one of the excursion events
  set E : ℕ → ℕ → Set Ω := fun n m =>
    {ω | ∃ k, 1 ≤ k ∧ ((n : ℝ) * ε / 2 - K0) / B ≤ ∑ i ∈ Finset.Icc 1 k, zz δ ε B m i ω}
    with hE
  have hcont : ∀ᵐ ω ∂μ, ω ∈ {ω | ∃ n, N0 ≤ n ∧ 1 ≤ n ∧ ε ≤ δ n ω} →
      ω ∈ ⋃ k : ℕ, ⋃ m ∈ Finset.Ico N1 (k + N0), E (k + N0) m := by
    filter_upwards [ae_bounds hrec] with ω ⟨h1, h2⟩ hω
    obtain ⟨n, hn0, hn1, hεn⟩ := hω
    obtain ⟨k, rfl⟩ : ∃ k, n = k + N0 := ⟨n - N0, by omega⟩
    have hN1n : N1 + 1 ≤ k + N0 := by
      have : N1 + 1 ≤ N0 := le_trans (le_max_left _ _) (le_max_right _ _)
      omega
    obtain ⟨m, hm1, hm2, hm3⟩ := pointwise_exc hε ha hb h1 h2 (by omega : 1 ≤ N1) hN1n hεn
    simp only [Set.mem_iUnion]
    refine ⟨k, m, Finset.mem_Ico.mpr ⟨hm1, hm2⟩, ?_⟩
    exact ⟨k + N0, by omega, hm3⟩
  have hsum : μ {ω | ∃ n, N0 ≤ n ∧ 1 ≤ n ∧ ε ≤ δ n ω} ≤
      ENNReal.ofReal (∑' k, f (k + N0)) := by
    have hsum' := (summable_nat_add_iff N0).mpr hfsum
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => hfnn _) hsum']
    refine (measure_mono_ae hcont).trans ((measure_iUnion_le _).trans ?_)
    refine ENNReal.tsum_le_tsum (fun k => ?_)
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hN2n : N2 ≤ k + N0 := by
      have : N2 ≤ N0 := le_max_left _ _
      omega
    calc ∑ m ∈ Finset.Ico N1 (k + N0), μ (E (k + N0) m)
        ≤ ∑ m ∈ Finset.Ico N1 (k + N0), ENNReal.ofReal (r ^ (k + N0)) := by
          refine Finset.sum_le_sum (fun m hm => ?_)
          exact hbd (k + N0) m hN2n (Finset.mem_Ico.mp hm).1
      _ = ((k + N0 - N1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (r ^ (k + N0)) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ ((k + N0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (r ^ (k + N0)) := by
          gcongr; omega
      _ = ENNReal.ofReal (f (k + N0)) := by
          rw [hf]; simp only
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hfin : μ {ω | ∃ n, N0 ≤ n ∧ 1 ≤ n ∧ ε ≤ δ n ω} ≠ ⊤ := measure_ne_top _ _
  have hS : ∑' k, f (k + N0) < ε / 2 := hN3 N0 (le_trans (le_max_right _ _) (le_max_right _ _))
  have hS0 : 0 ≤ ∑' k, f (k + N0) := tsum_nonneg (fun k => hfnn _)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
  rw [ENNReal.toReal_ofReal hS0] at this
  linarith

theorem blackwell_lemma_proof (a b c ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (δ : ℕ → Ω → ℝ), (∀ n, 1 ≤ n → Measurable (δ n)) → SatisfiesRecursion a b c μ δ →
        (μ {ω | ∃ n, N₀ ≤ n ∧ 1 ≤ n ∧ ε ≤ δ n ω}).toReal < ε := by
  obtain ⟨N₀, hN⟩ := lemma_core (max a 1) (max b 1) (max c 1) ε (le_max_right _ _)
    (le_max_right _ _) (le_max_right _ _) hε
  exact ⟨N₀, fun Ω _ μ _ δ hm h =>
    hN Ω μ δ hm (satisfiesRecursion_mono (le_max_left _ _) (le_max_left _ _) (le_max_left _ _) h)⟩

end Thm2'

end VectorPayoffs.Convex

open VectorPayoffs.Convex in
theorem solution (a b c ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (δ : ℕ → Ω → ℝ), (∀ n, 1 ≤ n → Measurable (δ n)) → SatisfiesRecursion a b c μ δ →
        (μ {ω | ∃ n, N₀ ≤ n ∧ 1 ≤ n ∧ ε ≤ δ n ω}).toReal < ε :=
  blackwell_lemma_proof a b c ε hε
