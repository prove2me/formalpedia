-- Prove2me | solution 1 for YeIPA.QPApprox.qp_min_sphere_rounding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T23:43:01.851834+00:00
-- url     : https://prove2.me/submissions/acc88e4e-02ff-48f6-815f-c79d9fdbd937

import Mathlib
import Definitions.Def_YeIPA_QPApprox_Relaxation

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

open Matrix MeasureTheory
open YeIPA.QPApprox

theorem solution {m n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (hfeas : ∃ x, IsQPFeasible A b x) :
    (∀ V : Matrix (Fin n) (Fin n) ℝ,
      (∀ i, frob (constrMat A i) (Vᵀ * V) = b i) → (∀ j, colNorm V j ≤ 1) →
      qpMin Q A b ≤ ∫ u, sigma (Vᵀ *ᵥ coords u) ⬝ᵥ
        ((colNormDiag V * Q * colNormDiag V) *ᵥ sigma (Vᵀ *ᵥ coords u)) ∂(sphereUniform n)) ∧
    ∃ V : Matrix (Fin n) (Fin n) ℝ,
      (∀ i, frob (constrMat A i) (Vᵀ * V) = b i) ∧ (∀ j, colNorm V j ≤ 1) ∧
      (∫ u, sigma (Vᵀ *ᵥ coords u) ⬝ᵥ
        ((colNormDiag V * Q * colNormDiag V) *ᵥ sigma (Vᵀ *ᵥ coords u)) ∂(sphereUniform n))
        = qpMin Q A b :=
  QR100.main Q hQ A b hfeas
