-- Prove2me | solution 1 for VectorPayoffs.Convex.blackwell_theorem2
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:56:42.336196+00:00
-- url     : https://prove2.me/submissions/764bf3b0-7adf-40d5-a6ab-d12682a142bd

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Recursion

/-!
Blackwell (1956), Theorem 2 (quoted from Blackwell 1954): a maximal inequality for sums of increments
with a negative conditional drift.

Proof.  Put `λ = log ((1 + u) / (1 - u))`, `S_k = z_1 + ⋯ + z_k` and `M_k = exp (λ S_k)`.
For `|z| ≤ 1` convexity of `exp` gives `exp (λ z) ≤ 1 + c (z + u |z|)` with `c = 2u / (1 - u²)`
(`exp_bound`).  Taking conditional expectations and using the drift hypothesis
`E(z_k | past) ≤ -u E(|z_k| | past)` shows that `M` is a nonnegative supermartingale with respect to
the natural filtration of `z` and `M_0 = 1`.  Ville's maximal inequality (`ville_ineq`, obtained from
optional stopping at the first time `M ≥ a`) gives `P(max_{k ≤ n} M_k ≥ a) ≤ 1 / a`; with
`a = exp (λ t)` and `1 / a = ((1 - u) / (1 + u)) ^ t`, and monotone continuity in `n`, the claim follows.
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

omit [MeasurableSpace Ω] in
theorem measurable_tuple_fun (z : ℕ → Ω → ℝ) (k : ℕ) (g : (Fin k → ℝ) → ℝ)
    (hg : Measurable g) :
    Measurable[pastSigma z k] (fun ω => g (fun i : Fin k => z (i.val + 1) ω)) :=
  @Measurable.comp _ _ _ (pastSigma z k) _ _ _ _ hg
    (Measurable.of_comap_le (le_refl (pastSigma z k)))

open scoped NNReal ENNReal in
theorem blackwell_theorem2_proof {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (z : ℕ → Ω → ℝ) (u : ℝ) (hu : 0 < u) (hu1 : u < 1)
    (hmeas : ∀ k, 1 ≤ k → Measurable (z k))
    (hbound : ∀ k, 1 ≤ k → ∀ᵐ ω ∂μ, |z k ω| ≤ 1)
    (hdrift : ∀ k, 1 ≤ k →
      μ[z k | pastSigma z (k - 1)] ≤ᵐ[μ] (-u) • μ[fun ω => |z k ω| | pastSigma z (k - 1)])
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
  let 𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω) := pastFiltration z hmeas
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
    have : Measurable[pastSigma z k] (M k) := by
      have := measurable_tuple_fun z k (fun v => Real.exp (lam * ∑ i, v i))
        (Real.measurable_exp.comp ((Finset.measurable_sum _
          (fun i _ => measurable_pi_apply i)).const_mul lam))
      convert this using 2 with ω
      simp only [M, S]
      rw [sum_Icc_eq_sum_fin]
    exact this.stronglyMeasurable
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
    have h4' : μ[z (k + 1) | pastSigma z k] ω ≤ -u * μ[fun ω => |z (k + 1) ω| | pastSigma z k] ω := by
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

end Thm2'

end VectorPayoffs.Convex

open VectorPayoffs.Convex in
theorem solution {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (z : ℕ → Ω → ℝ) (u : ℝ) (hu : 0 < u) (hu1 : u < 1)
    (hmeas : ∀ k, 1 ≤ k → Measurable (z k))
    (hbound : ∀ k, 1 ≤ k → ∀ᵐ ω ∂μ, |z k ω| ≤ 1)
    (hdrift : ∀ k, 1 ≤ k →
      μ[z k | pastSigma z (k - 1)] ≤ᵐ[μ] (-u) • μ[fun ω => |z k ω| | pastSigma z (k - 1)])
    (t : ℝ) :
    μ {ω | ∃ k, 1 ≤ k ∧ t ≤ ∑ i ∈ Finset.Icc 1 k, z i ω} ≤
      ENNReal.ofReal (((1 - u) / (1 + u)) ^ t) :=
  blackwell_theorem2_proof μ z u hu hu1 hmeas hbound hdrift t
