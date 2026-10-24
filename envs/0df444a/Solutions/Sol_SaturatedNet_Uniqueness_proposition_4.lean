-- Prove2me | solution 1 for SaturatedNet.Uniqueness.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:37:43.450386+00:00
-- url     : https://prove2.me/submissions/5cfc8484-9d94-4193-a7c1-71e1f0aac196

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
import Theorems.Thm_SaturatedNet_Uniqueness_proposition_1_i


/- Complete local helper proofs from PowerNorm.lean. -/

open Matrix Filter Topology
open scoped Matrix.Norms.Operator ENNReal NNReal

namespace SaturatedNet.Uniqueness.ContractionProof

lemma exists_power_norm_lt_one {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hρ : specRad P < 1) :
    ∃ k : ℕ, ‖(P.map (algebraMap ℝ ℂ)) ^ k‖ < 1 := by
  let A := P.map (algebraMap ℝ ℂ)
  have hg := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius A
  obtain ⟨k, hk⟩ := (hg.eventually (gt_mem_nhds hρ)).exists
  refine ⟨k, ?_⟩
  have hbase : (‖A^k‖₊ : ℝ≥0∞) < 1 := by
    by_contra h
    have hr := ENNReal.rpow_le_rpow (le_of_not_gt h) (by positivity : 0 ≤ (1 / (k : ℝ)))
    simp only [ENNReal.one_rpow] at hr
    exact (not_lt_of_ge hr) hk
  exact_mod_cast hbase

end SaturatedNet.Uniqueness.ContractionProof


/- Complete local helper proofs from Difference.lean. -/

open Matrix

namespace SaturatedNet.Uniqueness.ContractionProof

lemma sat_abs_sub_le (a x y : ℝ) : |sat a x-sat a y| ≤ |x-y| := by
  apply le_trans (abs_min_sub_min_le_max (max x 0) a (max y 0) a)
  exact max_le (abs_max_sub_max_le_abs x y 0) (by simp)

lemma equilibrium_diff_le {n : Type*} [Fintype n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w c x y : n → ℝ)
    (hx : IsEquilibrium P w c x) (hy : IsEquilibrium P w c y) :
    (fun i => |x i-y i|) ≤ Matrix.vecMul (fun i => |x i-y i|) P := by
  intro i
  change |x i-y i| ≤ _
  rw [hx i, hy i]
  apply (sat_abs_sub_le _ _ _).trans
  have heq : inflow P c x i-inflow P c y i = ∑ j, (x j-y j)*P j i := by
    simp only [inflow, add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib, sub_mul]
  rw [heq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact le_of_eq (by simp [Matrix.vecMul, dotProduct, abs_mul, abs_of_nonneg (hP _ _)])

lemma vecMul_mono_nonnegative {n : Type*} [Fintype n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) {x y : n → ℝ} (hxy : x ≤ y) :
    Matrix.vecMul x P ≤ Matrix.vecMul y P := by
  intro i
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hxy j) (hP j i))

lemma le_vecMul_pow {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (v : n → ℝ)
    (hv : v ≤ Matrix.vecMul v P) : ∀ k : ℕ, v ≤ Matrix.vecMul v (P^k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h := hv.trans (vecMul_mono_nonnegative P hP ih)
    simpa only [Matrix.vecMul_vecMul, ← pow_succ] using h

end SaturatedNet.Uniqueness.ContractionProof


/- Complete local helper proofs from RowBound.lean. -/

open Matrix
open scoped Matrix.Norms.Operator

namespace SaturatedNet.Uniqueness.ContractionProof

lemma power_row_sum_le_norm {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (k : ℕ) (i : n) :
    ∑ j, (P^k) i j ≤ ‖(P.map (algebraMap ℝ ℂ))^k‖ := by
  let A := (P.map (algebraMap ℝ ℂ))^k
  have h : (∑ j, ‖A i j‖₊) ≤ ‖A‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i)
  have h' : (∑ j, ‖A i j‖) ≤ ‖A‖ := by
    simpa only [NNReal.coe_sum, coe_nnnorm] using (NNReal.coe_le_coe.mpr h)
  have heq : ∀ j, ‖A i j‖ = (P^k) i j := by
    intro j
    change ‖((P.map (algebraMap ℝ ℂ))^k) i j‖ = _
    rw [← Matrix.map_pow P (algebraMap ℝ ℂ) k]
    change ‖((P^k) i j : ℂ)‖ = (P^k) i j
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Matrix.pow_apply_nonneg hP k i j)]
  simpa only [heq] using h'

lemma vecMul_sum_bound {n : Type*} [Fintype n]
    (Q : Matrix n n ℝ) (v : n → ℝ) (hv : ∀ i, 0 ≤ v i) (a : ℝ)
    (hrow : ∀ i, ∑ j, Q i j ≤ a) :
    ∑ i, (Matrix.vecMul v Q) i ≤ a * ∑ i, v i := by
  calc
    ∑ i, (Matrix.vecMul v Q) i = ∑ j, v j * ∑ i, Q j i := by
      simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ j, v j*a := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hrow j) (hv j))
    _ = a * ∑ i, v i := by rw [← Finset.sum_mul, mul_comm]

end SaturatedNet.Uniqueness.ContractionProof


open Matrix
open scoped Matrix.Norms.Operator
open SaturatedNet.Uniqueness.ContractionProof

namespace SaturatedNet.Uniqueness

theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w : n → ℝ) (hw : 0 ≤ w) (c : n → ℝ) (hρ : specRad P < 1) :
    ∃! x, IsEquilibrium P w c x := by
  obtain ⟨x, hx⟩ := (proposition_1_i P hP w hw c).2.1
  refine ⟨x, hx.1, ?_⟩
  intro y hy
  let v : n → ℝ := fun i => |y i-x i|
  have hv : ∀ i, 0 ≤ v i := fun i => abs_nonneg _
  have hiter : ∀ k : ℕ, v ≤ Matrix.vecMul v (P^k) :=
    le_vecMul_pow P hP v (equilibrium_diff_le P hP w c y x hy hx.1)
  obtain ⟨k, hk⟩ := exists_power_norm_lt_one P hρ
  let a : ℝ := ‖(P.map (algebraMap ℝ ℂ))^k‖
  have hsum : ∑ i, v i ≤ a * ∑ i, v i := by
    exact (Finset.sum_le_sum (fun i _ => hiter k i)).trans
      (vecMul_sum_bound (P^k) v hv a (power_row_sum_le_norm P hP k))
  have hz : ∑ i, v i ≤ 0 := by
    change a < 1 at hk
    nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hv i)]
  funext i
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  exact le_antisymm ((Finset.single_le_sum (fun j _ => hv j) (Finset.mem_univ i)).trans hz) (hv i)


end SaturatedNet.Uniqueness
