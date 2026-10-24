-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P63.logDetNormEntropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T10:02:56.172395+00:00
-- url     : https://prove2.me/submissions/8fae381e-aaf7-486a-990b-285fc1391709

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
open MeasureTheory Set Filter Topology

namespace X7A17

noncomputable def phi (q x t : ℝ) : ℝ := (x / t - Real.log (1 + x / t)) * t ^ (q - 1)

lemma u_bounds {u : ℝ} (hu : 0 ≤ u) : 0 ≤ u - Real.log (1 + u) ∧ u - Real.log (1 + u) ≤ u ^ 2 := by
  have h1 : 0 < 1 + u := by linarith
  have a := Real.log_le_sub_one_of_pos h1
  have b := Real.one_sub_inv_le_log_of_pos h1
  refine ⟨by linarith, ?_⟩
  have : u - (1 - (1 + u)⁻¹) ≤ u ^ 2 := by
    rw [show u - (1 - (1 + u)⁻¹) = u ^ 2 / (1 + u) by field_simp; ring]
    rw [div_le_iff₀ h1]; nlinarith
  linarith

lemma phi_meas (q x : ℝ) : Measurable (phi q x) := by
  unfold phi; fun_prop

lemma phi_nonneg {q x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) : 0 ≤ phi q x t :=
  mul_nonneg (u_bounds (div_nonneg hx ht.le)).1 (Real.rpow_nonneg ht.le _)

lemma phi_le_small {q x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) : phi q x t ≤ x * t ^ (q - 2) := by
  unfold phi
  have h := (u_bounds (div_nonneg hx ht.le)).1
  have h2 : x / t - Real.log (1 + x / t) ≤ x / t := by
    have := Real.log_nonneg (show (1:ℝ) ≤ 1 + x / t by have := div_nonneg hx ht.le; linarith)
    linarith
  calc (x / t - Real.log (1 + x / t)) * t ^ (q - 1) ≤ x / t * t ^ (q - 1) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg ht.le _)
    _ = x * t ^ (q - 2) := by
        have e : t ^ (q - 2) = t ^ (q - 1) / t := by
          rw [← Real.rpow_sub_one ht.ne']; ring_nf
        rw [e]; field_simp

lemma phi_le_large {q x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) : phi q x t ≤ x ^ 2 * t ^ (q - 3) := by
  unfold phi
  have h2 := (u_bounds (div_nonneg hx ht.le)).2
  calc (x / t - Real.log (1 + x / t)) * t ^ (q - 1) ≤ (x / t) ^ 2 * t ^ (q - 1) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg ht.le _)
    _ = x ^ 2 * t ^ (q - 3) := by
        have e : t ^ (q - 3) = t ^ (q - 1) / t / t := by
          rw [← Real.rpow_sub_one ht.ne', ← Real.rpow_sub_one ht.ne']; ring_nf
        rw [e]; field_simp

lemma phi_integrable {q x : ℝ} (hq1 : 1 < q) (hq2 : q < 2) (hx : 0 ≤ x) :
    IntegrableOn (phi q x) (Ioi 0) := by
  have hsplit : Ioi (0:ℝ) = Ioo 0 1 ∪ Ici 1 := by
    ext t; simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]
    constructor
    · intro h; by_cases h1 : t < 1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (not_lt.mp h1)
    · rintro (⟨h, _⟩ | h) <;> linarith
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have hg : IntegrableOn (fun t : ℝ => x * t ^ (q - 2)) (Ioo 0 1) :=
      ((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ) < 1)).mpr (by linarith)).const_mul x
    refine hg.mono' (phi_meas q x).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (phi_nonneg hx ht.1)]
    exact phi_le_small hx ht.1
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have hg : IntegrableOn (fun t : ℝ => x ^ 2 * t ^ (q - 3)) (Ioi 1) :=
      ((integrableOn_Ioi_rpow_iff (by norm_num : (0:ℝ) < 1)).mpr (by linarith)).const_mul _
    refine hg.mono' (phi_meas q x).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0:ℝ) < t := lt_trans one_pos ht
    rw [Real.norm_eq_abs, abs_of_nonneg (phi_nonneg hx ht0)]
    exact phi_le_large hx ht0

lemma phi_scale {q x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    phi q x (x * s) = x ^ (q - 1) * phi q 1 s := by
  unfold phi
  rw [Real.mul_rpow hx.le hs.le]
  have : x / (x * s) = 1 / s := by field_simp
  rw [this]; ring

noncomputable def K (q : ℝ) : ℝ := ∫ t in Ioi 0, phi q 1 t

lemma phi_integral {q x : ℝ} (hq1 : 1 < q) (hx : 0 ≤ x) :
    ∫ t in Ioi 0, phi q x t = x ^ q * K q := by
  rcases hx.eq_or_lt with h | h
  · subst h
    have : ∀ t, phi q 0 t = 0 := fun t => by simp [phi]
    simp only [this, integral_zero]
    rw [Real.zero_rpow (by linarith), zero_mul]
  · have e := integral_comp_mul_left_Ioi (phi q x) 0 h
    rw [mul_zero] at e
    have e2 : ∫ s in Ioi (0:ℝ), phi q x (x * s) = ∫ s in Ioi (0:ℝ), x ^ (q - 1) * phi q 1 s :=
      setIntegral_congr_fun measurableSet_Ioi (fun s hs => phi_scale h hs)
    rw [e2, integral_const_mul] at e
    have : ∫ t in Ioi 0, phi q x t = x * (x ^ (q - 1) * K q) := by
      rw [K, e, smul_eq_mul]; field_simp
    rw [this, ← mul_assoc, ← Real.rpow_one_add' h.le (by linarith)]
    · congr 2; ring

lemma K_pos {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) : 0 < K q := by
  unfold K
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have : Ioi (0:ℝ) ⊆ Function.support (phi q 1) ∩ Ioi 0 := by
      intro t ht
      refine ⟨?_, ht⟩
      have ht' : (0:ℝ) < t := ht
      have hu : 0 < 1 / t := by positivity
      have hlt : Real.log (1 + 1 / t) < 1 / t := by
        have := Real.log_lt_sub_one_of_pos (show 0 < 1 + 1/t by linarith) (by linarith)
        linarith
      simp only [Function.mem_support, phi]
      exact mul_ne_zero (by linarith) (Real.rpow_pos_of_pos ht' _).ne'
    calc (0 : ENNReal) < volume (Ioi (0:ℝ)) := by simp
      _ ≤ _ := measure_mono this
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t ht => phi_nonneg zero_le_one ht)
  · exact phi_integrable hq1 hq2 zero_le_one

/-- Core inequality for `1 < q < 2`. -/
lemma core_q {ι : Type*} [Fintype ι] (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsum : ∑ i, a i = ∑ i, b i)
    (hord : ∀ t : ℝ, 0 < t → ∑ i, Real.log (t + b i) ≤ ∑ i, Real.log (t + a i))
    {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) : ∑ i, a i ^ q ≤ ∑ i, b i ^ q := by
  have hK := K_pos hq1 hq2
  have key : ∫ t in Ioi 0, (∑ i, phi q (a i) t - ∑ i, phi q (b i) t) ≤ 0 := by
    refine setIntegral_nonpos measurableSet_Ioi fun t ht => ?_
    have ht' : (0:ℝ) < t := ht
    have hl : ∀ x : ℝ, 0 ≤ x → Real.log (1 + x / t) = Real.log (t + x) - Real.log t := by
      intro x hx
      rw [← Real.log_div (by linarith) ht'.ne']; congr 1; field_simp
    have expand : ∀ c : ι → ℝ, (∀ i, 0 ≤ c i) → ∑ i, phi q (c i) t =
        ((∑ i, c i) / t - (∑ i, Real.log (t + c i)) + Fintype.card ι * Real.log t) *
          t ^ (q - 1) := by
      intro c hc
      simp only [phi, ← Finset.sum_mul]
      congr 1
      simp only [hl _ (hc _), Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring
    rw [expand a ha, expand b hb, hsum, ← sub_mul]
    apply mul_nonpos_of_nonpos_of_nonneg _ (Real.rpow_nonneg ht'.le _)
    linarith [hord t ht']
  rw [integral_sub, integral_finsetSum, integral_finsetSum] at key
  · simp only [phi_integral hq1 (ha _), phi_integral hq1 (hb _), ← Finset.sum_mul] at key
    nlinarith
  · exact fun i _ => phi_integrable hq1 hq2 (hb i)
  · exact fun i _ => phi_integrable hq1 hq2 (ha i)
  · exact integrable_finsetSum _ fun i _ => phi_integrable hq1 hq2 (ha i)
  · exact integrable_finsetSum _ fun i _ => phi_integrable hq1 hq2 (hb i)


lemma core_all {ι : Type*} [Fintype ι] (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsum : ∑ i, a i = ∑ i, b i)
    (hord : ∀ t : ℝ, 0 < t → ∑ i, Real.log (t + b i) ≤ ∑ i, Real.log (t + a i))
    {q : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 2) : ∑ i, a i ^ q ≤ ∑ i, b i ^ q := by
  rcases hq2.lt_or_eq with h | h
  · exact core_q a b ha hb hsum hord hq1 h
  · subst h
    have hc : ∀ c : ι → ℝ, ContinuousAt (fun q : ℝ => ∑ i, c i ^ q) 2 := fun c =>
      by
        have : ∀ i, ContinuousAt (fun q : ℝ => c i ^ q) 2 := fun i =>
          Real.continuousAt_const_rpow' (by norm_num)
        fun_prop
    have hlim : Tendsto (fun q : ℝ => ∑ i, b i ^ q - ∑ i, a i ^ q) (𝓝[<] 2)
        (𝓝 (∑ i, b i ^ (2:ℝ) - ∑ i, a i ^ (2:ℝ))) :=
      ((hc b).sub (hc a)).tendsto.mono_left nhdsWithin_le_nhds
    have := ge_of_tendsto hlim (by
      filter_upwards [Ioo_mem_nhdsLT (show (1:ℝ) < 2 by norm_num)] with q hq
      exact sub_nonneg.mpr (core_q a b ha hb hsum hord hq.1 hq.2))
    linarith

lemma term_deriv {a : ℝ} (ha : 0 ≤ a) : HasDerivAt (fun q : ℝ => a ^ q) (a * Real.log a) 1 := by
  rcases ha.eq_or_lt with h | h
  · subst h
    simp only [Real.log_zero, mul_zero]
    apply (hasDerivAt_const (1:ℝ) (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds (show (0:ℝ) < 1 by norm_num)] with q hq
    exact Real.zero_rpow hq.ne'
  · have := (Real.hasStrictDerivAt_const_rpow h 1).hasDerivAt
    simpa using this

lemma core_ent {ι : Type*} [Fintype ι] (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsum : ∑ i, a i = ∑ i, b i)
    (hord : ∀ t : ℝ, 0 < t → ∑ i, Real.log (t + b i) ≤ ∑ i, Real.log (t + a i)) :
    ∑ i, a i * Real.log (a i) ≤ ∑ i, b i * Real.log (b i) := by
  set h : ℝ → ℝ := fun q => ∑ i, b i ^ q - ∑ i, a i ^ q with hh
  have hd : HasDerivAt h (∑ i, b i * Real.log (b i) - ∑ i, a i * Real.log (a i)) 1 :=
    (HasDerivAt.fun_sum fun i _ => term_deriv (hb i)).sub (HasDerivAt.fun_sum fun i _ => term_deriv (ha i))
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsGT_le_nhdsNE (1:ℝ))
  have h1 : h 1 = 0 := by simp [hh, hsum]
  have := ge_of_tendsto hs (by
    filter_upwards [Ioo_mem_nhdsGT (show (1:ℝ) < 2 by norm_num)] with q hq
    rw [slope_def_field, h1, sub_zero]
    apply div_nonneg _ (by linarith [hq.1])
    simp only [hh]
    exact sub_nonneg.mpr (core_q a b ha hb hsum hord hq.1 hq.2))
  linarith


open QAlgorithms.Papers.Independent.Information100.P63
open scoped Matrix ComplexConjugate ComplexOrder

lemma eigen_eq {I : Type*} [Fintype I] [DecidableEq I] {X : Matrix I I ℂ} (hX : X.IsHermitian)
    (j : Fin (Fintype.card I)) : eigen X j = hX.eigenvalues₀ j := by
  unfold eigen QAlgorithms.ascEigenvalues
  rw [dif_pos hX]; simp

lemma sum_eigen {I : Type*} [Fintype I] [DecidableEq I] {X : Matrix I I ℂ} (hX : X.IsHermitian)
    (f : ℝ → ℝ) : ∑ j, f (eigen X j) = ∑ i, f (hX.eigenvalues i) := by
  simp only [eigen_eq hX, Matrix.IsHermitian.eigenvalues]
  exact (Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun j => f (hX.eigenvalues₀ j))).symm

lemma cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma det_shift {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (t : ℝ) : ((t : ℂ) • (1 : Matrix n n ℂ) + X).det = ∏ i, ((t + hX.eigenvalues i : ℝ) : ℂ) := by
  set U := hX.eigenvectorUnitary
  have hspec := hX.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hUU : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 :=
    Unitary.mul_star_self_of_mem U.2
  have e : (t : ℂ) • (1 : Matrix n n ℂ) + X =
      (U : Matrix n n ℂ) * Matrix.diagonal (fun i => ((t + hX.eigenvalues i : ℝ) : ℂ)) *
        star (U : Matrix n n ℂ) := by
    have hd : Matrix.diagonal (fun i => ((t + hX.eigenvalues i : ℝ) : ℂ)) =
        (t : ℂ) • (1 : Matrix n n ℂ) + Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues) := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    conv_lhs => rw [hspec]
    rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU]
  rw [e, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
    Unitary.star_mul_self_of_mem U.2, Matrix.det_one, one_mul, Matrix.det_diagonal]

lemma logDet_eq {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.PosSemidef)
    {t : ℝ} (ht : 0 < t) : logDet t X = ∑ i, Real.log (t + hX.isHermitian.eigenvalues i) := by
  unfold logDet
  rw [det_shift hX.isHermitian t, ← Complex.ofReal_prod, Complex.ofReal_re, Real.log_prod]
  intro i _
  have := hX.eigenvalues_nonneg i
  exact (by linarith : (0:ℝ) < t + _).ne'

lemma vn_eq {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    QAlgorithms.vnEntropy X = -∑ i, hX.eigenvalues i * Real.logb 2 (hX.eigenvalues i) := by
  unfold QAlgorithms.vnEntropy
  rw [cfc_trace hX, ← Complex.ofReal_sum, Complex.ofReal_re]

lemma sum_eig_one {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : QAlgorithms.IsDensityMatrix X) : ∑ i, hX.1.isHermitian.eigenvalues i = 1 := by
  have h := hX.1.isHermitian.trace_eq_sum_eigenvalues
  have := congrArg Complex.re (h.symm.trans hX.2)
  simp only [Complex.one_re] at this
  rw [Complex.re_sum] at this; simpa using this

end X7A17

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P63 X7A17 in
theorem solution (D : ℕ) (hD : 0 < D) (X Y : Mat (Fin D))
    (hX : IsDensityMatrix X) (hY : IsDensityMatrix Y)
    (horder : ∀ t : ℝ, 0 < t → logDet t Y ≤ logDet t X) :
    (∀ q : ℝ, 1 < q → q ≤ 2 → schatten q X ≤ schatten q Y) ∧
    vnEntropy Y ≤ vnEntropy X := by
  set a := hX.1.isHermitian.eigenvalues
  set b := hY.1.isHermitian.eigenvalues
  have ha : ∀ i, 0 ≤ a i := hX.1.eigenvalues_nonneg
  have hb : ∀ i, 0 ≤ b i := hY.1.eigenvalues_nonneg
  have hsum : ∑ i, a i = ∑ i, b i := by rw [sum_eig_one hX, sum_eig_one hY]
  have hord : ∀ t : ℝ, 0 < t → ∑ i, Real.log (t + b i) ≤ ∑ i, Real.log (t + a i) := by
    intro t ht
    have := horder t ht
    rwa [logDet_eq hX.1 ht, logDet_eq hY.1 ht] at this
  refine ⟨fun q hq1 hq2 => ?_, ?_⟩
  · unfold schatten
    rw [sum_eigen hX.1.isHermitian (fun x => x ^ q), sum_eigen hY.1.isHermitian (fun x => x ^ q)]
    exact Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (ha i) _)
      (core_all a b ha hb hsum hord hq1 hq2) (by positivity)
  · rw [vn_eq hX.1.isHermitian, vn_eq hY.1.isHermitian]
    have key := core_ent a b ha hb hsum hord
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have e : ∀ c : Fin D → ℝ, ∑ i, c i * Real.logb 2 (c i) = (∑ i, c i * Real.log (c i)) / Real.log 2 := by
      intro c; rw [Finset.sum_div]; congr 1; ext i; rw [Real.logb]; ring
    change -∑ i, b i * Real.logb 2 (b i) ≤ -∑ i, a i * Real.logb 2 (a i)
    rw [e a, e b, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right key hl.le
