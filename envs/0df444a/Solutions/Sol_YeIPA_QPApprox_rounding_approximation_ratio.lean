-- Prove2me | solution 1 for YeIPA.QPApprox.rounding_approximation_ratio
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T23:55:39.293724+00:00
-- url     : https://prove2.me/submissions/b17c25f2-0a0d-4d04-b042-356979b9e585

import Mathlib
import Definitions.Def_YeIPA_QPApprox_Relaxation
import Theorems.Thm_YeIPA_QPApprox_sdp_range_approximates_qp
import Theorems.Thm_YeIPA_QPApprox_qp_relaxation_sandwich
import Theorems.Thm_YeIPA_QPApprox_arcsin_entrywise_dominates

open Matrix MeasureTheory

namespace QR100
open YeIPA.QPApprox
open scoped Pointwise

theorem M_toSphere_univ_ne_zero {n : ℕ} (hn : 0 < n) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ ≠ 0 := by
  rw [Measure.toSphere_apply_univ]
  refine mul_ne_zero ?_ ?_
  · simp [finrank_euclideanSpace]; omega
  · exact (Metric.isOpen_ball.measure_pos _ ⟨0, by simp⟩).ne'

theorem M_toSphere_univ_ne_top {n : ℕ} :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ ≠ ⊤ := by
  rw [Measure.toSphere_apply_univ]
  exact ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne

theorem sphere_prob {n : ℕ} (hn : 0 < n) : IsProbabilityMeasure (sphereUniform n) := by
  constructor
  rw [sphereUniform, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (M_toSphere_univ_ne_zero hn) M_toSphere_univ_ne_top

theorem sphere_null {n : ℕ} (hn : 0 < n) :
    sphereUniform n {u | coords u ⟨0, hn⟩ = 0} = 0 := by
  rw [sphereUniform, Measure.smul_apply, smul_eq_mul]
  have hS : MeasurableSet {u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
      coords u ⟨0, hn⟩ = 0} := by
    apply IsClosed.measurableSet
    apply isClosed_eq _ continuous_const
    exact (EuclideanSpace.proj (⟨0, hn⟩ : Fin n)).continuous.comp continuous_subtype_val
  rw [Measure.toSphere_apply' _ hS]
  have hsub : Set.Ioo (0 : ℝ) 1 • ((↑) '' {u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
      coords u ⟨0, hn⟩ = 0}) ⊆
      ((LinearMap.ker (EuclideanSpace.proj (⟨0, hn⟩ : Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).toLinearMap :
        Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))) := by
    rintro x ⟨r, -, y, ⟨u, hu, rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq, coords] at hu
    simp [hu]
  have hne : LinearMap.ker ((EuclideanSpace.proj (⟨0, hn⟩ : Fin n) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).toLinearMap) ≠ ⊤ := by
    intro h
    have : EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ) ∈
        LinearMap.ker ((EuclideanSpace.proj (⟨0, hn⟩ : Fin n) :
          EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).toLinearMap) := h ▸ Submodule.mem_top
    simp at this
  rw [measure_mono_null hsub (Measure.addHaar_submodule _ _ hne)]
  simp

end QR100


open Matrix MeasureTheory

namespace QR100
open YeIPA.QPApprox

variable {m n : ℕ}

theorem feas_bound (Q : Matrix (Fin n) (Fin n) ℝ) {x : Fin n → ℝ} (hx : ∀ j, |x j| ≤ 1) :
    |quadForm Q x| ≤ ∑ i, ∑ j, |Q i j| := by
  unfold quadForm
  simp only [dotProduct, mulVec]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  calc |x i| * |∑ j, Q i j * x j| ≤ 1 * ∑ j, |Q i j| := by
        refine mul_le_mul (hx i) ?_ (abs_nonneg _) zero_le_one
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        calc |Q i j| * |x j| ≤ |Q i j| * 1 := mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _)
          _ = |Q i j| := mul_one _
    _ = ∑ j, |Q i j| := one_mul _

theorem feas_abs {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {x : Fin n → ℝ}
    (hx : IsQPFeasible A b x) (j : Fin n) : |x j| ≤ 1 := abs_le.mpr (hx.2 j)

theorem bdd (Q : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    BddBelow (quadForm Q '' {x | IsQPFeasible A b x}) := by
  refine ⟨-(∑ i, ∑ j, |Q i j|), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := feas_bound Q (feas_abs hx)
  linarith [neg_abs_le (quadForm Q x)]

theorem quadForm_cont (Q : Matrix (Fin n) (Fin n) ℝ) : Continuous (quadForm Q) := by
  unfold quadForm
  simp only [dotProduct, mulVec]
  fun_prop

theorem exists_min (Q : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hfeas : ∃ x, IsQPFeasible A b x) :
    ∃ x, IsQPFeasible A b x ∧ quadForm Q x = qpMin Q A b := by
  set K := {x | IsQPFeasible A b x} with hK
  have hclosed : IsClosed K := by
    have : K = (⋂ i, {x : Fin n → ℝ | ∑ j, A i j * x j ^ 2 = b i}) ∩
        ⋂ j, {x : Fin n → ℝ | -1 ≤ x j ∧ x j ≤ 1} := by
      ext x; simp [hK, IsQPFeasible]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_eq
        (continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).pow 2))
        continuous_const)
      (isClosed_iInter fun j => IsClosed.inter (isClosed_le continuous_const (continuous_apply j))
        (isClosed_le (continuous_apply j) continuous_const))
  have hbdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    rw [Real.norm_eq_abs]
    exact feas_abs hx j
  have hcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  obtain ⟨x0, hx0⟩ := hfeas
  obtain ⟨x, hxK, hmin⟩ := hcpt.exists_isMinOn ⟨x0, hx0⟩ (quadForm_cont Q).continuousOn
  refine ⟨x, hxK, ?_⟩
  symm
  refine IsLeast.csInf_eq ⟨⟨x, hxK, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hmin hy

theorem frob_eq (A : Matrix (Fin m) (Fin n) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) (i : Fin m) :
    frob (constrMat A i) (Vᵀ * V) = ∑ j, A i j * colNorm V j ^ 2 := by
  unfold frob constrMat colNorm
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
  simp only [diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    mul_apply, transpose_apply, sq]

theorem colNorm_nonneg (V : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : 0 ≤ colNorm V j :=
  Real.sqrt_nonneg _

theorem sign_abs (t : ℝ) : |sign t| = 1 := by
  unfold sign; split_ifs <;> norm_num

theorem rounded_feas (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (V : Matrix (Fin n) (Fin n) ℝ)
    (h1 : ∀ i, frob (constrMat A i) (Vᵀ * V) = b i) (h2 : ∀ j, colNorm V j ≤ 1) (y : Fin n → ℝ) :
    IsQPFeasible A b (colNormDiag V *ᵥ sigma y) := by
  have hx : ∀ j, (colNormDiag V *ᵥ sigma y) j = colNorm V j * sign (y j) := by
    intro j; simp [colNormDiag, mulVec_diagonal, sigma]
  have habs : ∀ j, |(colNormDiag V *ᵥ sigma y) j| ≤ 1 := by
    intro j
    rw [hx, abs_mul, sign_abs, mul_one, abs_of_nonneg (colNorm_nonneg V j)]
    exact h2 j
  refine ⟨fun i => ?_, fun j => abs_le.mp (habs j)⟩
  rw [← h1 i, frob_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hx, mul_pow]
  have : sign (y j) ^ 2 = 1 := by
    have := sign_abs (y j)
    rw [← sq_abs, this, one_pow]
  rw [this, mul_one]

theorem integrand_eq (Q V : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ) :
    s ⬝ᵥ ((colNormDiag V * Q * colNormDiag V) *ᵥ s) = quadForm Q (colNormDiag V *ᵥ s) := by
  have hT : (colNormDiag V)ᵀ = colNormDiag V := by simp [colNormDiag]
  unfold quadForm
  conv_lhs => rw [← hT]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, hT]

theorem sign_meas : Measurable sign := by
  unfold sign
  exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
    measurable_const

theorem integrand_meas (Q V : Matrix (Fin n) (Fin n) ℝ) :
    Measurable (fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      quadForm Q (colNormDiag V *ᵥ sigma (Vᵀ *ᵥ coords u))) := by
  have hcoord : ∀ k, Continuous (fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      coords u k) := fun k => (EuclideanSpace.proj k).continuous.comp continuous_subtype_val
  have hc : Continuous (fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => Vᵀ *ᵥ coords u) := by
    refine continuous_pi fun j => ?_
    simp only [mulVec, dotProduct]
    exact continuous_finsetSum _ fun k _ => continuous_const.mul (hcoord k)
  have hs : Measurable (sigma : (Fin n → ℝ) → Fin n → ℝ) := by
    unfold sigma
    exact measurable_pi_lambda _ fun j => sign_meas.comp (measurable_pi_apply j)
  have hq : Continuous (fun s : Fin n → ℝ => quadForm Q (colNormDiag V *ᵥ s)) :=
    (quadForm_cont Q).comp (continuous_pi fun j => by
      simp only [mulVec, dotProduct]
      exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_apply k))
  exact hq.measurable.comp (hs.comp hc.measurable)

theorem rank1_round (x : Fin n → ℝ) {t : ℝ} (ht : t ≠ 0) :
    (fun j => |x j| * sign (x j * t)) = if 0 < t then x else -x := by
  funext j
  unfold sign
  rcases lt_or_gt_of_ne ht with ht | ht
  · rw [if_neg (not_lt.mpr ht.le)]
    simp only [Pi.neg_apply]
    by_cases hx : 0 < x j
    · have : ¬ (0 ≤ x j * t) := not_le.mpr (mul_neg_of_pos_of_neg hx ht)
      rw [if_neg this, abs_of_pos hx]; ring
    · have hx' : x j ≤ 0 := not_lt.mp hx
      rw [if_pos (mul_nonneg_of_nonpos_of_nonpos hx' ht.le), abs_of_nonpos hx']; ring
  · rw [if_pos ht]
    by_cases hx : 0 ≤ x j
    · rw [if_pos (mul_nonneg hx ht.le), abs_of_nonneg hx]; ring
    · have hx' : x j < 0 := not_le.mp hx
      have : ¬ (0 ≤ x j * t) := not_le.mpr (mul_neg_of_neg_of_pos hx' ht)
      rw [if_neg this, abs_of_neg hx']; ring

theorem quadForm_neg (Q : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadForm Q (-x) = quadForm Q x := by
  simp [quadForm, mulVec_neg]

theorem main (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (hfeas : ∃ x, IsQPFeasible A b x) :
    (∀ V : Matrix (Fin n) (Fin n) ℝ,
      (∀ i, frob (constrMat A i) (Vᵀ * V) = b i) → (∀ j, colNorm V j ≤ 1) →
      qpMin Q A b ≤ ∫ u, sigma (Vᵀ *ᵥ coords u) ⬝ᵥ
        ((colNormDiag V * Q * colNormDiag V) *ᵥ sigma (Vᵀ *ᵥ coords u)) ∂(sphereUniform n)) ∧
    ∃ V : Matrix (Fin n) (Fin n) ℝ,
      (∀ i, frob (constrMat A i) (Vᵀ * V) = b i) ∧ (∀ j, colNorm V j ≤ 1) ∧
      (∫ u, sigma (Vᵀ *ᵥ coords u) ⬝ᵥ
        ((colNormDiag V * Q * colNormDiag V) *ᵥ sigma (Vᵀ *ᵥ coords u)) ∂(sphereUniform n))
        = qpMin Q A b := by
  simp only [integrand_eq]
  obtain ⟨x, hx, hxmin⟩ := exists_min Q A b hfeas
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : ∀ y : Fin 0 → ℝ, quadForm Q y = 0 := fun y => by simp [quadForm]
    have hq : qpMin Q A b = 0 := by rw [← hxmin, h0]
    refine ⟨fun V _ _ => by simp [h0, hq], 0, ?_, ?_, by simp [h0, hq]⟩
    · intro i
      have := hx.1 i
      simp at this
      simp [frob, ← this]
    · intro j; exact j.elim0
  have := sphere_prob hn
  set C := ∑ i, ∑ j, |Q i j|
  have hint : ∀ V : Matrix (Fin n) (Fin n) ℝ, (∀ i, frob (constrMat A i) (Vᵀ * V) = b i) →
      (∀ j, colNorm V j ≤ 1) → Integrable (fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        quadForm Q (colNormDiag V *ᵥ sigma (Vᵀ *ᵥ coords u))) (sphereUniform n) := by
    intro V h1 h2
    refine Integrable.of_bound (integrand_meas Q V).aestronglyMeasurable C (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs]
    exact feas_bound Q (feas_abs (rounded_feas A b V h1 h2 _))
  refine ⟨fun V h1 h2 => ?_, ?_⟩
  · have hc : ∫ _u, qpMin Q A b ∂(sphereUniform n) = qpMin Q A b := by simp
    rw [← hc]
    refine integral_mono (integrable_const _) (hint V h1 h2) fun u => ?_
    exact csInf_le (bdd Q A b) ⟨_, rounded_feas A b V h1 h2 _, rfl⟩
  · set i0 : Fin n := ⟨0, hn⟩
    set V : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k j => if k = i0 then x j else 0 with hVdef
    have hcol : ∀ j, colNorm V j = |x j| := by
      intro j
      unfold colNorm
      rw [Finset.sum_eq_single i0 (fun k _ hk => by simp [hVdef, hk]) (by simp)]
      simp [hVdef, Real.sqrt_sq_eq_abs]
    have h1 : ∀ i, frob (constrMat A i) (Vᵀ * V) = b i := by
      intro i
      rw [frob_eq, ← hx.1 i]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hcol, sq_abs]
    have h2 : ∀ j, colNorm V j ≤ 1 := fun j => by rw [hcol]; exact feas_abs hx j
    refine ⟨V, h1, h2, ?_⟩
    have hae : ∀ᵐ u ∂(sphereUniform n), coords u i0 ≠ 0 := by
      rw [ae_iff]
      simpa using sphere_null hn
    have hpt : ∀ u, coords u i0 ≠ 0 →
        quadForm Q (colNormDiag V *ᵥ sigma (Vᵀ *ᵥ coords u)) = qpMin Q A b := by
      intro u hu
      have hv : colNormDiag V *ᵥ sigma (Vᵀ *ᵥ coords u) = fun j => |x j| * sign (x j * coords u i0) := by
        funext j
        simp only [colNormDiag, mulVec_diagonal, sigma, hcol]
        congr 2
        simp [mulVec, dotProduct, hVdef, transpose_apply, i0]
      rw [hv, rank1_round x hu, ← hxmin]
      split_ifs
      · rfl
      · exact quadForm_neg Q x
    rw [integral_congr_ae (hae.mono fun u hu => hpt u hu)]
    simp

end QR100


section G100
open MeasureTheory ProbabilityTheory Real Set

noncomputable def g72mnb_sg (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

lemma g72mnb_sg_meas : Measurable g72mnb_sg := by
  unfold g72mnb_sg
  exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
    measurable_const

lemma g72mnb_sg_abs (t : ℝ) : |g72mnb_sg t| = 1 := by
  unfold g72mnb_sg; split_ifs <;> simp

lemma g72mnb_sg_sq (t : ℝ) : g72mnb_sg t * g72mnb_sg t = 1 := by
  unfold g72mnb_sg; split_ifs <;> norm_num

lemma g72mnb_piece (f : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b) (h : ∀ x ∈ Ioo a b, f x = c) :
    IntervalIntegrable f volume a b ∧ ∫ x in a..b, f x = (b - a) * c := by
  have hI : IntegrableOn f (Ioo a b) := by
    refine (continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
      (fun x hx => (h x hx).symm) measurableSet_Ioo
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hI, ?_⟩
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo h, setIntegral_const]
  simp [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]

lemma g72mnb_angle (φ : ℝ) (h0 : 0 ≤ φ) (hπ : φ ≤ π) :
    ∫ θ in (-π)..π, g72mnb_sg (cos θ) * g72mnb_sg (cos (θ - φ)) = 2 * π - 4 * φ := by
  set f := fun θ => g72mnb_sg (cos θ) * g72mnb_sg (cos (θ - φ)) with hf
  have hper : Function.Periodic f (2 * π) := by
    intro θ; simp only [hf]
    rw [cos_add_two_pi, show θ + 2 * π - φ = (θ - φ) + 2 * π by ring, cos_add_two_pi]
  have e1 : ∫ θ in (-π)..π, f θ = ∫ θ in (-(π / 2))..(-(π / 2) + 2 * π), f θ := by
    have := hper.intervalIntegral_add_eq (-π) (-(π / 2))
    rw [show -π + 2 * π = π by ring] at this; exact this
  have pos : ∀ x, x ∈ Ioo (-(π / 2)) (π / 2) → g72mnb_sg (cos x) = 1 := fun x hx => by
    unfold g72mnb_sg; rw [if_pos (cos_pos_of_mem_Ioo hx).le]
  have neg : ∀ x, x - π ∈ Ioo (-(π / 2)) (π / 2) → g72mnb_sg (cos x) = -1 := fun x hx => by
    have := cos_pos_of_mem_Ioo hx; rw [cos_sub_pi] at this
    unfold g72mnb_sg; rw [if_neg (by linarith)]
  have neg' : ∀ x, x + π ∈ Ioo (-(π / 2)) (π / 2) → g72mnb_sg (cos x) = -1 := fun x hx => by
    have := cos_pos_of_mem_Ioo hx; rw [cos_add_pi] at this
    unfold g72mnb_sg; rw [if_neg (by linarith)]
  obtain ⟨i1, v1⟩ := g72mnb_piece f (-(π / 2)) (φ - π / 2) (-1) (by linarith) (fun x hx => by
    simp only [hf]
    rw [pos x ⟨hx.1, by linarith [hx.2]⟩, neg' (x - φ) ⟨by linarith [hx.1], by linarith [hx.2]⟩]
    ring)
  obtain ⟨i2, v2⟩ := g72mnb_piece f (φ - π / 2) (π / 2) 1 (by linarith) (fun x hx => by
    simp only [hf]
    rw [pos x ⟨by linarith [hx.1], hx.2⟩, pos (x - φ) ⟨by linarith [hx.1], by linarith [hx.2]⟩]
    ring)
  obtain ⟨i3, v3⟩ := g72mnb_piece f (π / 2) (φ + π / 2) (-1) (by linarith) (fun x hx => by
    simp only [hf]
    rw [neg x ⟨by linarith [hx.1], by linarith [hx.2]⟩,
      pos (x - φ) ⟨by linarith [hx.1], by linarith [hx.2]⟩]
    ring)
  obtain ⟨i4, v4⟩ := g72mnb_piece f (φ + π / 2) (-(π / 2) + 2 * π) 1 (by linarith) (fun x hx => by
    simp only [hf]
    rw [neg x ⟨by linarith [hx.1], by linarith [hx.2]⟩,
      neg (x - φ) ⟨by linarith [hx.1], by linarith [hx.2]⟩]
    ring)
  rw [e1, ← intervalIntegral.integral_add_adjacent_intervals i1 (i2.trans (i3.trans i4)),
    ← intervalIntegral.integral_add_adjacent_intervals i2 (i3.trans i4),
    ← intervalIntegral.integral_add_adjacent_intervals i3 i4, v1, v2, v3, v4]
  ring

noncomputable def g72mnb_phi (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

lemma g72mnb_phi_mul (a b : ℝ) :
    g72mnb_phi a * g72mnb_phi b = (2 * π)⁻¹ * exp (-(a ^ 2 + b ^ 2) / 2) := by
  simp only [g72mnb_phi, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = (2 * π)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  calc _ = ((√(2 * π))⁻¹ * (√(2 * π))⁻¹) * (exp (-a ^ 2 / 2) * exp (-b ^ 2 / 2)) := by ring
    _ = _ := by rw [this, ← exp_add]; ring_nf

lemma g72mnb_polar (F : ℝ × ℝ → ℝ) (Θ : ℝ → ℝ)
    (hF : ∀ r θ, 0 < r → F (r * cos θ, r * sin θ) = Θ θ) :
    ∫ p : ℝ × ℝ, F p * (g72mnb_phi p.1 * g72mnb_phi p.2) =
      (∫ r in Ioi (0 : ℝ), r * ((2 * π)⁻¹ * exp (-(r ^ 2) / 2))) * ∫ θ in Ioo (-π) π, Θ θ := by
  rw [← integral_comp_polarCoord_symm, polarCoord_target,
    show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, ← setIntegral_prod_mul]
  refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun p hp => ?_)
  obtain ⟨r, θ⟩ := p
  simp only [polarCoord_symm_apply, smul_eq_mul]
  rw [hF r θ hp.1, g72mnb_phi_mul]
  have : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by nlinarith [sin_sq_add_cos_sq θ]
  rw [this]; ring

lemma g72mnb_R : (∫ r in Ioi (0 : ℝ), r * ((2 * π)⁻¹ * exp (-(r ^ 2) / 2))) * (2 * π) = 1 := by
  have h := g72mnb_polar (fun _ => 1) (fun _ => 1) (fun _ _ _ => rfl)
  have h1 : ∫ p : ℝ × ℝ, (fun _ => (1 : ℝ)) p * (g72mnb_phi p.1 * g72mnb_phi p.2) = 1 := by
    simp only [one_mul]
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, integral_prod_mul]
    have : ∫ x, g72mnb_phi x = 1 := integral_gaussianPDFReal_eq_one 0 one_ne_zero
    rw [this]; norm_num
  rw [h1, setIntegral_const] at h
  have h2 : volume.real (Ioo (-π) π) = 2 * π := by
    simp [Measure.real, Real.volume_Ioo]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [h2, smul_eq_mul, mul_one] at h
  exact h.symm

lemma g72mnb_2d (φ : ℝ) (h0 : 0 ≤ φ) (hπ : φ ≤ π) :
    ∫ p : ℝ × ℝ, g72mnb_sg p.1 * g72mnb_sg (cos φ * p.1 + sin φ * p.2) *
      (g72mnb_phi p.1 * g72mnb_phi p.2) = 1 - 2 * φ / π := by
  rw [g72mnb_polar _ (fun θ => g72mnb_sg (cos θ) * g72mnb_sg (cos (θ - φ)))]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos]),
      g72mnb_angle φ h0 hπ]
    have hR := g72mnb_R
    have hpi := pi_pos
    set R := ∫ r in Ioi (0 : ℝ), r * ((2 * π)⁻¹ * exp (-(r ^ 2) / 2))
    have : R = 1 / (2 * π) := by field_simp; linarith
    rw [this]; field_simp; ring
  · intro r θ hr
    simp only
    have e : cos φ * (r * cos θ) + sin φ * (r * sin θ) = r * cos (θ - φ) := by
      rw [cos_sub]; ring
    rw [e]
    unfold g72mnb_sg
    simp only [mul_nonneg_iff_of_pos_left hr]

open Matrix

lemma g72mnb_prod_gauss (f : ℝ × ℝ → ℝ) (hf : Measurable f) (hb : ∀ p, |f p| ≤ 1) :
    ∫ p, f p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      ∫ p : ℝ × ℝ, f p * (g72mnb_phi p.1 * g72mnb_phi p.2) := by
  have hφm : Measurable g72mnb_phi := measurable_gaussianPDFReal 0 1
  have hφi : Integrable g72mnb_phi := integrable_gaussianPDFReal 0 1
  have hφ0 : ∀ x, 0 ≤ g72mnb_phi x := fun x => gaussianPDFReal_nonneg 0 1 x
  have hI1 : Integrable f ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    Integrable.mono' (integrable_const 1) hf.aestronglyMeasurable
      (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hb p)
  have hI2 : Integrable (fun p : ℝ × ℝ => f p * (g72mnb_phi p.1 * g72mnb_phi p.2))
      ((volume : Measure ℝ).prod volume) := by
    refine Integrable.mono' (hφi.mul_prod hφi)
      (hf.mul ((hφm.comp measurable_fst).mul (hφm.comp measurable_snd))).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hφ0 _) (hφ0 _))]
    exact mul_le_of_le_one_left (mul_nonneg (hφ0 _) (hφ0 _)) (hb p)
  rw [integral_prod _ hI1, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    integral_prod _ hI2, integral_gaussianReal_eq_integral_smul one_ne_zero]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [smul_eq_mul]
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [smul_eq_mul, g72mnb_phi]; ring

noncomputable def g72mnb_L {n : ℕ} (u v : Fin n → ℝ) (x : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![u ⬝ᵥ x, v ⬝ᵥ x]

noncomputable def g72mnb_M (c s : ℝ) (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![p.1, c * p.1 + s * p.2]

lemma g72mnb_inner2 (a b : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2)) t = a * t 0 + b * t 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

lemma g72mnb_L_meas {n : ℕ} (u v : Fin n → ℝ) : Measurable (g72mnb_L u v) := by
  unfold g72mnb_L; fun_prop

lemma g72mnb_M_meas (c s : ℝ) : Measurable (g72mnb_M c s) := by
  unfold g72mnb_M; fun_prop

lemma g72mnb_cf_L {n : ℕ} (u v : Fin n → ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    charFun ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map (g72mnb_L u v)) t =
      Complex.exp (-((∑ i, (t 0 * u i + t 1 * v i) ^ 2 : ℝ) : ℂ) / 2) := by
  set w : Fin n → ℝ := fun i => t 0 * u i + t 1 * v i
  have h1 : charFun ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map (g72mnb_L u v)) t =
      charFun ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map (WithLp.toLp 2))
        (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin n)) := by
    rw [charFun_apply, charFun_apply, integral_map (g72mnb_L_meas u v).aemeasurable (by fun_prop),
      integral_map (by fun_prop) (by fun_prop)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    congr 3
    rw [g72mnb_L, g72mnb_inner2]
    simp [PiLp.inner_apply, w, dotProduct, Finset.mul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h1, charFun_pi]
  simp only [charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp [w, Finset.sum_neg_distrib]
  rw [neg_div, Finset.sum_div]

lemma g72mnb_cf_M (c s : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    charFun (((gaussianReal 0 1).prod (gaussianReal 0 1)).map (g72mnb_M c s)) t =
      Complex.exp (-(((t 0 + t 1 * c) ^ 2 + (t 1 * s) ^ 2 : ℝ) : ℂ) / 2) := by
  rw [charFun_apply, integral_map (g72mnb_M_meas c s).aemeasurable (by fun_prop)]
  have h : ∀ p : ℝ × ℝ, Complex.exp (inner ℝ (g72mnb_M c s p) t * Complex.I) =
      Complex.exp (((t 0 + t 1 * c : ℝ) : ℂ) * p.1 * Complex.I) *
        Complex.exp (((t 1 * s : ℝ) : ℂ) * p.2 * Complex.I) := by
    intro p
    rw [← Complex.exp_add, g72mnb_M, g72mnb_inner2]
    congr 1; push_cast; ring
  simp_rw [h]
  rw [integral_prod_mul (f := fun x : ℝ => Complex.exp (((t 0 + t 1 * c : ℝ) : ℂ) * x * Complex.I))
    (g := fun y : ℝ => Complex.exp (((t 1 * s : ℝ) : ℂ) * y * Complex.I)),
    ← charFun_apply_real, ← charFun_apply_real, charFun_gaussianReal, charFun_gaussianReal,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma g72mnb_law {n : ℕ} (u v : Fin n → ℝ) (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (c s : ℝ)
    (hc : u ⬝ᵥ v = c) (hcs : c ^ 2 + s ^ 2 = 1) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).map (g72mnb_L u v) =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (g72mnb_M c s) := by
  haveI := Measure.isProbabilityMeasure_map (μ := Measure.pi fun _ : Fin n => gaussianReal 0 1)
    (g72mnb_L_meas u v).aemeasurable
  haveI := Measure.isProbabilityMeasure_map (μ := (gaussianReal 0 1).prod (gaussianReal 0 1))
    (g72mnb_M_meas c s).aemeasurable
  apply Measure.ext_of_charFun
  funext t
  rw [g72mnb_cf_L, g72mnb_cf_M]
  have e : ∑ i, (t 0 * u i + t 1 * v i) ^ 2 =
      t 0 ^ 2 * (u ⬝ᵥ u) + 2 * t 0 * t 1 * (u ⬝ᵥ v) + t 1 ^ 2 * (v ⬝ᵥ v) := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (t 0 * u i + t 1 * v i) ^ 2 = (t 0 + t 1 * c) ^ 2 + (t 1 * s) ^ 2 := by
    rw [e, hu, hv, hc]
    linear_combination (-(t 1) ^ 2) * hcs
  rw [e2]

lemma g72mnb_cs {n : ℕ} (u v : Fin n → ℝ) (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) :
    -1 ≤ u ⬝ᵥ v ∧ u ⬝ᵥ v ≤ 1 := by
  have a : 0 ≤ ∑ i, (u i - v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have b : 0 ≤ ∑ i, (u i + v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have ea : ∑ i, (u i - v i) ^ 2 = u ⬝ᵥ u - 2 * (u ⬝ᵥ v) + v ⬝ᵥ v := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have eb : ∑ i, (u i + v i) ^ 2 = u ⬝ᵥ u + 2 * (u ⬝ᵥ v) + v ⬝ᵥ v := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  constructor <;> nlinarith

lemma g72mnb_ident {n : ℕ} (u v : Fin n → ℝ) (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) :
    ∫ x, g72mnb_sg (u ⬝ᵥ x) * g72mnb_sg (v ⬝ᵥ x) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      2 / π * arcsin (u ⬝ᵥ v) := by
  obtain ⟨h1, h2⟩ := g72mnb_cs u v hu hv
  set φ := arccos (u ⬝ᵥ v) with hφ
  have hc : cos φ = u ⬝ᵥ v := cos_arccos h1 h2
  have hcs : cos φ ^ 2 + sin φ ^ 2 = 1 := by rw [add_comm]; exact sin_sq_add_cos_sq φ
  let G : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => g72mnb_sg (z 0) * g72mnb_sg (z 1)
  have hG : Measurable G :=
    (g72mnb_sg_meas.comp (by fun_prop)).mul (g72mnb_sg_meas.comp (by fun_prop))
  have step1 : ∫ x, g72mnb_sg (u ⬝ᵥ x) * g72mnb_sg (v ⬝ᵥ x)
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      ∫ z, G z ∂((Measure.pi fun _ : Fin n => gaussianReal 0 1).map (g72mnb_L u v)) := by
    rw [integral_map (g72mnb_L_meas u v).aemeasurable hG.aestronglyMeasurable]
    simp [G, g72mnb_L]
  rw [step1, g72mnb_law u v hu hv (cos φ) (sin φ) hc.symm hcs,
    integral_map (g72mnb_M_meas _ _).aemeasurable hG.aestronglyMeasurable]
  have e : (fun p => G (g72mnb_M (cos φ) (sin φ) p)) =
      fun p : ℝ × ℝ => g72mnb_sg p.1 * g72mnb_sg (cos φ * p.1 + sin φ * p.2) := by
    funext p; simp [G, g72mnb_M]
  rw [e, g72mnb_prod_gauss _ (by
      exact (g72mnb_sg_meas.comp measurable_fst).mul (g72mnb_sg_meas.comp (by fun_prop)))
      (fun p => by rw [abs_mul, g72mnb_sg_abs, g72mnb_sg_abs]; norm_num),
    g72mnb_2d φ (arccos_nonneg _) (arccos_le_pi _), arcsin_eq_pi_div_two_sub_arccos, ← hφ]
  have := pi_pos
  field_simp


open scoped MatrixOrder
end G100


open Matrix MeasureTheory ProbabilityTheory

namespace RA100
open YeIPA.QPApprox

theorem TR_polar {n : ℕ} (hn : 0 < n) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ∀ (c : ℝ), 0 < c → ∀ x, F (c • x) = F x) (g : ℝ → ℝ) :
    ∫ x, F x * g ‖x‖ ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      (∫ u, F u ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) *
        ∫ r, g r.1 ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← integral_prod_mul]
  rw [← (Measure.measurePreserving_homeomorphUnitSphereProd
    (volume : Measure (EuclideanSpace ℝ (Fin n)))).integral_comp
    (Homeomorph.measurableEmbedding _) (fun p => F p.1 * g p.2.1)]
  rw [show ∫ x, F x * g ‖x‖ ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      ∫ x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))), F x * g ‖(x : EuclideanSpace ℝ (Fin n))‖
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).comap (↑)) from by
    rw [integral_subtype_comap (measurableSet_singleton _).compl (fun x => F x * g ‖x‖),
      restrict_compl_singleton]]
  congr 1
  funext ⟨x, hx⟩
  have : 0 < ‖x‖ := by simpa using hx
  simp [homeomorphUnitSphereProd_apply_fst_coe, hF _ (inv_pos.2 this)]

noncomputable def TR_rho {n : ℕ} (y : Fin n → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (y i)

theorem TR_rho_nonneg {n : ℕ} (y : Fin n → ℝ) : 0 ≤ TR_rho y :=
  Finset.prod_nonneg fun _ _ => gaussianPDFReal_nonneg _ _ _

theorem TR_rho_meas {n : ℕ} : Measurable (TR_rho : (Fin n → ℝ) → ℝ) := by
  unfold TR_rho
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)

theorem TR_pi_gauss {n : ℕ} :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun y => ENNReal.ofReal (TR_rho y)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi]
  simp_rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => setIntegral_nonneg_of_ae
      (ae_of_all _ fun x => gaussianPDFReal_nonneg 0 1 x)),
    ← integral_fintype_prod_eq_prod (fun _ => gaussianPDFReal 0 1),
    ofReal_integral_eq_lintegral_ofReal]
  · rfl
  · exact Integrable.fintype_prod fun i => (integrable_gaussianPDFReal 0 1).restrict
  · exact ae_of_all _ fun y => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _

theorem TR_gauss_int {n : ℕ} (h : (Fin n → ℝ) → ℝ) :
    ∫ y, h y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      ∫ x : EuclideanSpace ℝ (Fin n), h (WithLp.ofLp x) * TR_rho (WithLp.ofLp x) := by
  rw [TR_pi_gauss, integral_withDensity_eq_integral_toReal_smul (TR_rho_meas.ennreal_ofReal)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    ← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).integral_comp']
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (TR_rho_nonneg _), smul_eq_mul, mul_comm]
  rfl

theorem TR_rho_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    TR_rho (WithLp.ofLp x) = (Real.sqrt (2 * Real.pi))⁻¹ ^ n * Real.exp (-‖x‖ ^ 2 / 2) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [TR_rho, gaussianPDFReal, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
  congr 2
  · simp
  · rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    simp [neg_div]

theorem TR_key {n : ℕ} (hn : 0 < n) (h : (Fin n → ℝ) → ℝ)
    (hh : ∀ (c : ℝ), 0 < c → ∀ x, h (c • x) = h x) :
    ∫ y, h y ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      (∫ u, h (WithLp.ofLp (u : EuclideanSpace ℝ (Fin n)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) *
        ∫ r, (Real.sqrt (2 * Real.pi))⁻¹ ^ n * Real.exp (-r.1 ^ 2 / 2)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)) := by
  rw [TR_gauss_int]
  simp_rw [TR_rho_norm]
  exact TR_polar hn (fun x => h (WithLp.ofLp x))
    (fun c hc x => by simpa using hh c hc (WithLp.ofLp x))
    (fun r => (Real.sqrt (2 * Real.pi))⁻¹ ^ n * Real.exp (-r ^ 2 / 2))

theorem transfer {n : ℕ} (hn : 0 < n) (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) (C : ℝ)
    (hb : ∀ x, |f x| ≤ C) (hh : ∀ (c : ℝ), 0 < c → ∀ x, f (c • x) = f x) :
    ∫ x, f x ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      ∫ u, f (coords u) ∂(sphereUniform n) := by
  have h1 := TR_key hn (fun _ => 1) (fun _ _ _ => rfl)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
  rw [TR_key hn f hh, sphereUniform, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  rw [Measure.real] at h1
  rw [mul_comm]
  congr 1
  rw [mul_one] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

end RA100


open Matrix MeasureTheory ProbabilityTheory

namespace RA100
open YeIPA.QPApprox

variable {m n : ℕ}

theorem sign_pos_mul {c : ℝ} (hc : 0 < c) (t : ℝ) : sign (c * t) = sign t := by
  unfold sign
  by_cases h : 0 ≤ t
  · rw [if_pos (mul_nonneg hc.le h), if_pos h]
  · rw [if_neg (fun h' => h (nonneg_of_mul_nonneg_right h' hc)), if_neg h]

theorem sign_eq_sg (t : ℝ) : sign t = g72mnb_sg t := rfl

theorem sphere_sign (hn : 0 < n) (a b : Fin n → ℝ) (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1) :
    ∫ u, sign (a ⬝ᵥ coords u) * sign (b ⬝ᵥ coords u) ∂(sphereUniform n) =
      2 / Real.pi * Real.arcsin (a ⬝ᵥ b) := by
  have hm : Measurable (fun x : Fin n → ℝ => sign (a ⬝ᵥ x) * sign (b ⬝ᵥ x)) :=
    (QR100.sign_meas.comp (by fun_prop)).mul (QR100.sign_meas.comp (by fun_prop))
  rw [← transfer hn (fun x => sign (a ⬝ᵥ x) * sign (b ⬝ᵥ x)) hm 1
    (fun x => by rw [abs_mul, QR100.sign_abs, QR100.sign_abs]; norm_num)
    (fun c hc x => by simp only [dotProduct_smul, smul_eq_mul, sign_pos_mul hc])]
  exact g72mnb_ident a b ha hb

/-- column `i` of `V` -/
def col (V : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : Fin n → ℝ := fun k => V k i

theorem col_dot (V : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : col V i ⬝ᵥ col V i = colNorm V i ^ 2 := by
  unfold colNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
  simp [col, dotProduct, sq]

/-- normalized columns (a fixed unit vector for zero columns) -/
noncomputable def w (hn : 0 < n) (V : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : Fin n → ℝ :=
  if colNorm V i = 0 then Pi.single ⟨0, hn⟩ 1 else (colNorm V i)⁻¹ • col V i

theorem w_unit (hn : 0 < n) (V : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : w hn V i ⬝ᵥ w hn V i = 1 := by
  unfold w
  split_ifs with h
  · simp
  · rw [smul_dotProduct, dotProduct_smul, col_dot, smul_eq_mul, smul_eq_mul]
    field_simp

theorem col_eq (hn : 0 < n) (V : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    col V i = colNorm V i • w hn V i := by
  unfold w
  split_ifs with h
  · have h0 : col V i ⬝ᵥ col V i = 0 := by rw [col_dot, h]; ring
    rw [h, zero_smul]
    exact dotProduct_self_eq_zero.mp h0
  · rw [smul_smul, mul_inv_cancel₀ h, one_smul]

/-- correlation matrix -/
noncomputable def C (hn : 0 < n) (V : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => w hn V i ⬝ᵥ w hn V j

theorem C_psd (hn : 0 < n) (V : Matrix (Fin n) (Fin n) ℝ) : (C hn V).PosSemidef := by
  set W : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k i => w hn V i k with hW
  have : C hn V = Wᴴ * W := by
    ext i j
    rw [mul_apply]
    simp [C, hW, dotProduct, conjTranspose_apply]
  rw [this]
  exact posSemidef_conjTranspose_mul_self W

theorem C_diag (hn : 0 < n) (V : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : C hn V j j = 1 :=
  w_unit hn V j

theorem X_eq (hn : 0 < n) (V : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (Vᵀ * V) i j = colNorm V i * colNorm V j * C hn V i j := by
  have : (Vᵀ * V) i j = col V i ⬝ᵥ col V j := by
    simp [mul_apply, col, dotProduct, transpose_apply]
  rw [this, col_eq hn V i, col_eq hn V j, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  simp only [C]; ring

theorem s_eq (hn : 0 < n) (V : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (hi : colNorm V i ≠ 0)
    (c : Fin n → ℝ) : sign (col V i ⬝ᵥ c) = sign (w hn V i ⬝ᵥ c) := by
  rw [col_eq hn V i, smul_dotProduct, smul_eq_mul]
  exact sign_pos_mul (lt_of_le_of_ne (QR100.colNorm_nonneg V i) (Ne.symm hi)) _

/-- the expected second-moment matrix of the rounded point -/
noncomputable def Y (hn : 0 < n) (V : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => colNorm V i * colNorm V j * (2 / Real.pi * Real.arcsin (C hn V i j))

theorem s_meas (a : Fin n → ℝ) :
    Measurable (fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => sign (a ⬝ᵥ coords u)) := by
  have hcoord : ∀ k, Continuous (fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      coords u k) := fun k => (EuclideanSpace.proj k).continuous.comp continuous_subtype_val
  have : Continuous (fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => a ⬝ᵥ coords u) := by
    simp only [dotProduct]
    exact continuous_finsetSum _ fun k _ => continuous_const.mul (hcoord k)
  exact QR100.sign_meas.comp this.measurable

theorem ss_int (hn : 0 < n) (a b : Fin n → ℝ) (c : ℝ) :
    Integrable (fun u => c * (sign (a ⬝ᵥ coords u) * sign (b ⬝ᵥ coords u))) (sphereUniform n) := by
  have := QR100.sphere_prob hn
  refine Integrable.const_mul ?_ c
  refine Integrable.of_bound ((s_meas a).mul (s_meas b)).aestronglyMeasurable 1 (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, QR100.sign_abs, QR100.sign_abs]; norm_num

theorem expect (hn : 0 < n) (Q V : Matrix (Fin n) (Fin n) ℝ) :
    ∫ u, quadForm Q (roundedPoint V u) ∂(sphereUniform n) = frob Q (Y hn V) := by
  have hpt : ∀ u, quadForm Q (roundedPoint V u) = ∑ i, ∑ j,
      Q i j * colNorm V i * colNorm V j * (sign (col V i ⬝ᵥ coords u) * sign (col V j ⬝ᵥ coords u)) := by
    intro u
    have hr : ∀ i, roundedPoint V u i = colNorm V i * sign (col V i ⬝ᵥ coords u) := by
      intro i
      simp only [roundedPoint, colNormDiag, mulVec_diagonal, sigma]
      rfl
    simp only [quadForm, dotProduct, mulVec, hr, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [hpt]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ss_int hn _ _ _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => ss_int hn _ _ _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  simp only [Y]
  by_cases hi : colNorm V i = 0
  · rw [hi]; ring
  by_cases hj : colNorm V j = 0
  · rw [hj]; ring
  have : ∫ u, sign (col V i ⬝ᵥ coords u) * sign (col V j ⬝ᵥ coords u) ∂(sphereUniform n) =
      2 / Real.pi * Real.arcsin (C hn V i j) := by
    simp only [s_eq hn V i hi, s_eq hn V j hj]
    exact sphere_sign hn _ _ (w_unit hn V i) (w_unit hn V j)
  rw [this]; ring

noncomputable def Z (hn : 0 < n) (V : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (2 / (Real.pi - 2)) • (colNormDiag V * (entrywise Real.arcsin (C hn V) - C hn V) * colNormDiag V)

theorem Z_apply (hn : 0 < n) (V : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Z hn V i j = 2 / (Real.pi - 2) *
      (colNorm V i * colNorm V j * (Real.arcsin (C hn V i j) - C hn V i j)) := by
  simp only [Z, colNormDiag, Matrix.smul_apply, diagonal_mul, mul_diagonal, Matrix.sub_apply,
    smul_eq_mul]
  simp only [entrywise]
  ring

theorem pi_gt_two : 2 < Real.pi := by linarith [Real.pi_gt_three]

theorem Z_psd (hn : 0 < n) (V : Matrix (Fin n) (Fin n) ℝ) : (Z hn V).PosSemidef := by
  have h1 := arcsin_entrywise_dominates (C hn V) (C_psd hn V)
    (fun j => by simp [diagVec, C_diag])
  have h2 := h1.conjTranspose_mul_mul_same (colNormDiag V)
  have hT : (colNormDiag V)ᴴ = colNormDiag V := by
    simp [colNormDiag, diagonal_conjTranspose]
  rw [hT] at h2
  have hc : (0 : ℝ) ≤ 2 / (Real.pi - 2) := by
    have := pi_gt_two; positivity
  exact h2.smul hc

theorem Z_diag (hn : 0 < n) (V : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    Z hn V j j = (Vᵀ * V) j j := by
  rw [Z_apply, X_eq hn V, C_diag, Real.arcsin_one]
  have := pi_gt_two
  have h1 : Real.pi - 2 ≠ 0 := by linarith
  field_simp

theorem Y_decomp (hn : 0 < n) (V : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Y hn V i j = 2 / Real.pi * (Vᵀ * V) i j + (1 - 2 / Real.pi) * Z hn V i j := by
  rw [Z_apply, X_eq hn V]
  simp only [Y]
  have := pi_gt_two
  have h1 : Real.pi - 2 ≠ 0 := by linarith
  have h2 : Real.pi ≠ 0 := by linarith
  field_simp
  ring

theorem frob_constr (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (M : Matrix (Fin n) (Fin n) ℝ) :
    frob (constrMat A i) M = ∑ j, A i j * M j j := by
  unfold frob constrMat
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [diagonal_apply]

theorem main (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (hfeas : ∃ x, IsQPFeasible A b x)
    (X V : Matrix (Fin n) (Fin n) ℝ) (hX : IsRelaxOptimal Q A b X) (hV : Vᵀ * V = X) :
    ((∫ u, quadForm Q (roundedPoint V u) ∂(sphereUniform n)) - qpMin Q A b) /
        (qpMax Q A b - qpMin Q A b) ≤ Real.pi / 2 - 1 ∧
      Real.pi / 2 - 1 < 4 / 7 := by
  have hpi3 := Real.pi_gt_three
  refine ⟨?_, by linarith [Real.pi_lt_d4]⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : ∀ Q' : Matrix (Fin 0) (Fin 0) ℝ, qpMin Q' A b = 0 := by
      intro Q'
      obtain ⟨x, _, hx⟩ := QR100.exists_min Q' A b hfeas
      rw [← hx]; simp [quadForm]
    simp [qpMax, h0]
    linarith
  set a := ∫ u, quadForm Q (roundedPoint V u) ∂(sphereUniform n) with ha_def
  have ha : a = frob Q (Y hn V) := expect hn Q V
  have hpl : sdpMin Q A b = frob Q X := by
    refine IsLeast.csInf_eq ⟨⟨X, hX.1, rfl⟩, ?_⟩
    rintro _ ⟨X', hX', rfl⟩
    exact hX.2 X' hX'
  have hZf : IsRelaxFeasible A b (Z hn V) := by
    refine ⟨fun i => ?_, fun j => ?_, Z_psd hn V⟩
    · rw [frob_constr, ← hX.1.1 i, frob_constr]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Z_diag, hV]
    · simp only [diagVec]; rw [Z_diag, hV]; exact hX.1.2.1 j
  have hY : frob Q (Y hn V) = 2 / Real.pi * frob Q X + (1 - 2 / Real.pi) * frob Q (Z hn V) := by
    unfold frob
    simp only [Y_decomp, hV, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_ <;> ring
  have hsand := qp_relaxation_sandwich Q hQ A b hfeas
  have hrange := sdp_range_approximates_qp Q hQ A b hfeas
  have hZ : frob Q (Z hn V) ≤ sdpMax Q A b := hsand.2.1.1 _ hZf
  have hlow : qpMin Q A b ≤ a := by
    have hcol : ∀ j, colNorm V j ≤ 1 := by
      intro j
      unfold colNorm
      rw [Real.sqrt_le_one]
      have := hX.1.2.1 j
      simp only [diagVec, ← hV, mul_apply, transpose_apply] at this
      simpa [sq] using this
    have := (QR100.main Q hQ A b hfeas).1 V (fun i => by rw [hV]; exact hX.1.1 i) hcol
    simp only [QR100.integrand_eq] at this
    exact this
  have h3 := hrange.2.1
  obtain ⟨h4, h5, _⟩ := hsand.2.2
  set ql := qpMin Q A b
  set qu := qpMax Q A b
  set pl := sdpMin Q A b
  set pu := sdpMax Q A b
  have hk : (0 : ℝ) ≤ Real.pi / 2 - 1 := by linarith
  have hk1 : Real.pi / 2 - 1 ≤ 1 := by linarith [Real.pi_lt_d4]
  have hA : a - pl ≤ (1 - 2 / Real.pi) * (pu - pl) := by
    rw [ha, hY, hpl]
    have : (0 : ℝ) ≤ 1 - 2 / Real.pi := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    nlinarith [mul_le_mul_of_nonneg_left hZ this]
  have hB : (1 - 2 / Real.pi) * (pu - pl) ≤ (Real.pi / 2 - 1) * (qu - pl) := by
    have := mul_le_mul_of_nonneg_left h3 hk
    have e : (Real.pi / 2 - 1) * (2 / Real.pi * (pu - pl)) = (1 - 2 / Real.pi) * (pu - pl) := by
      field_simp
    linarith
  have hC : (Real.pi / 2 - 1) * (ql - pl) ≤ ql - pl := by
    have h := sub_nonneg.mpr h4
    nlinarith
  have key : a - ql ≤ (Real.pi / 2 - 1) * (qu - ql) := by nlinarith
  rcases eq_or_lt_of_le h5 with heq | hlt
  · rw [heq, sub_self, div_zero]; exact hk
  · rw [div_le_iff₀ (sub_pos.mpr hlt)]
    linarith

end RA100

open Matrix MeasureTheory
open YeIPA.QPApprox

theorem solution {m n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (hfeas : ∃ x, IsQPFeasible A b x)
    (X V : Matrix (Fin n) (Fin n) ℝ) (hX : IsRelaxOptimal Q A b X) (hV : Vᵀ * V = X) :
    ((∫ u, quadForm Q (roundedPoint V u) ∂(sphereUniform n)) - qpMin Q A b) /
        (qpMax Q A b - qpMin Q A b) ≤ Real.pi / 2 - 1 ∧
      Real.pi / 2 - 1 < 4 / 7 :=
  RA100.main Q hQ A b hfeas X V hX hV
