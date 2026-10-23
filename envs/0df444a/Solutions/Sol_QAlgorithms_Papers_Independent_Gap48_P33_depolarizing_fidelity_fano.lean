-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P33.depolarizing_fidelity_fano
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T23:03:27.620929+00:00
-- url     : https://prove2.me/submissions/051550e5-97f1-4ba6-bb7a-a6055f19af2a

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33



open Polynomial

namespace X6G41D

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma spec_sub (d : n → ℝ) : spectrum ℝ (Matrix.diagonal (fun i => (d i : ℂ))) ⊆ Set.range d := by
  intro μ hμ
  by_contra hc
  rw [spectrum.mem_iff] at hμ
  apply hμ
  have e : (μ • 1 : Matrix n n ℂ) = Matrix.diagonal (fun _ => (μ : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Complex.real_smul]
    · simp [Matrix.one_apply, h]
  rw [Algebra.algebraMap_eq_smul_one, e, Matrix.diagonal_sub,
    Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro i
  simp only [isUnit_iff_ne_zero, ne_eq, sub_eq_zero]
  intro h
  apply hc
  refine ⟨i, ?_⟩
  have := congrArg Complex.re h
  simpa using this.symm

lemma aeval_diag (d : n → ℝ) (P : ℝ[X]) :
    aeval (Matrix.diagonal (fun i => (d i : ℂ))) P =
      Matrix.diagonal (fun i => ((P.eval (d i) : ℝ) : ℂ)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, Matrix.diagonal_add]
  | monomial k a =>
    rw [aeval_monomial, Matrix.diagonal_pow, Algebra.algebraMap_eq_smul_one, smul_one_mul,
      ← Matrix.diagonal_smul]
    congr 1; funext i
    simp only [eval_monomial, Pi.smul_apply, Pi.pow_apply, Complex.real_smul]
    push_cast; ring

lemma cfc_diag (d : n → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  classical
  set S := Finset.univ.image d
  set P := Lagrange.interpolate S id f
  have hP : ∀ i, P.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f)
      (Set.injOn_id _) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    rwa [id] at this
  have hsa : IsSelfAdjoint (Matrix.diagonal (fun i => (d i : ℂ))) := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  rw [cfc_congr (g := fun t => P.eval t), cfc_polynomial P _ hsa, aeval_diag]
  · congr 1; funext i; rw [hP]
  · intro t ht
    obtain ⟨i, rfl⟩ := spec_sub d ht
    exact (hP i).symm

end X6G41D

namespace X6P33F
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P33
open Real

theorem vn_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ unitary (Matrix ι ι ℂ)) (d : ι → ℝ) :
    vnEntropy (U * Matrix.diagonal (fun i => (d i : ℂ)) * star U) =
      ∑ i, negMulLog (d i) / log 2 := by
  set D := Matrix.diagonal (fun i => (d i : ℂ))
  have hD : IsSelfAdjoint D := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  set u : unitary (Matrix ι ι ℂ) := ⟨U, hU⟩
  set φ := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) u
  have hst : U * D * star U = φ D := rfl
  have hφD : IsSelfAdjoint (φ D) := by
    rw [IsSelfAdjoint, ← map_star, hD.star_eq]
  have hcont : ContinuousOn (fun x : ℝ => x * Real.logb 2 x) (spectrum ℝ D) :=
    ((Set.finite_range _).subset (X6G41D.spec_sub _)).continuousOn _
  unfold vnEntropy
  rw [hst, ← StarAlgHomClass.map_cfc φ _ D hcont (by
      show Continuous fun x : Matrix ι ι ℂ => U * x * star U
      exact (continuous_const.mul continuous_id).mul continuous_const) hD hφD, X6G41D.cfc_diag]
  simp only [φ, Unitary.conjStarAlgAut_apply]
  change -(Matrix.trace (U * _ * star U)).re = _
  rw [Matrix.trace_mul_cycle, Unitary.star_mul_self_of_mem hU, one_mul, Matrix.trace_diagonal,
    Complex.re_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.ofReal_re, Real.logb, negMulLog]
  ring

open QAlgorithms.Papers.Independent.Dependency50.P40 in
theorem refFid_eq {R A : Type*} [Fintype R] [Fintype A] (N : Superop A A)
    (psi : EuclideanSpace ℂ (R × A)) :
    referenceFidelity N psi = (∑ x, ∑ y, (starRingEnd ℂ) (psi x) *
      idTensorSuperop N (pureDensity psi) x y * psi y).re := by
  simp only [referenceFidelity, purificationFidelity, complexQuadraticForm]
  congr 1
  set e := (Fintype.equivFin R).prodCongr (Fintype.equivFin A)
  rw [← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [e, idTensorSuperop, pureDensity]; rfl

theorem fid (p q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    referenceFidelity (pauliDepolarizing p) (qBasis 0 q) = 1 - p + (p / 3) * (1 - 2 * q) ^ 2 := by
  have s1 : ((Real.sqrt q : ℂ)) ^ 2 = (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq]
  have s2 : ((Real.sqrt (1 - q) : ℂ)) ^ 2 = 1 - (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
  rw [refFid_eq]
  have : (∑ x, ∑ y, (starRingEnd ℂ) ((qBasis 0 q) x) *
      idTensorSuperop (pauliDepolarizing p) (pureDensity (qBasis 0 q)) x y * (qBasis 0 q) y) =
      ((1 - p + (p / 3) * (1 - 2 * q) ^ 2 : ℝ) : ℂ) := by
    simp [Fintype.sum_prod_type, Fintype.sum_bool, idTensorSuperop, pauliDepolarizing, pureDensity,
      qBasis, pauliX, pauliY, pauliZ, Matrix.mul_apply, Matrix.diagonal]
    ring_nf
    simp only [s1, s2]
    have s1' : ((Real.sqrt q : ℂ)) ^ 4 = (q : ℂ) ^ 2 := by
      rw [show 4 = 2 * 2 from rfl, pow_mul, s1]
    have s2' : ((Real.sqrt (1 - q) : ℂ)) ^ 4 = (1 - (q : ℂ)) ^ 2 := by
      rw [show 4 = 2 * 2 from rfl, pow_mul, s2]
    rw [s1', s2']
    push_cast
    ring
  rw [this, Complex.ofReal_re]

def e : Bool × Bool → Fin 4
  | (false, false) => 0
  | (false, true) => 1
  | (true, false) => 2
  | (true, true) => 3

noncomputable def U : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun x j => qBasis (e j) (1 / 2) x

noncomputable def dd (p : ℝ) : Bool × Bool → ℝ := fun j => if j = (false, false) then 1 - p else p / 3

theorem shalf : ((Real.sqrt (1 / 2) : ℝ) : ℂ) * ((Real.sqrt (1 / 2) : ℝ) : ℂ) = 1 / 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring

theorem sq1 : ((Real.sqrt (1 / 2) : ℝ) : ℂ) ^ 2 = 1 / 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring

theorem sq2 : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ^ 2 = 1 / 2 := by
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring

theorem U_unitary : U ∈ unitary (Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [U, e, qBasis, Matrix.mul_apply, Fintype.sum_prod_type, h] <;>
    ring_nf <;> simp only [sq1, sq2] <;> norm_num

theorem M_eq (p : ℝ) : depolarizingOutput p (1 / 2) =
    U * Matrix.diagonal (fun j => (dd p j : ℂ)) * star U := by
  have h : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [depolarizingOutput, idTensorSuperop, pauliDepolarizing, pureDensity, pauliX, pauliY,
      pauliZ, U, e, dd, qBasis, Matrix.mul_apply, Fintype.sum_prod_type, h, Matrix.diagonal] <;>
    ring_nf <;> (try simp only [sq1, sq2, Complex.I_sq]) <;> ring_nf

theorem vn_half (p : ℝ) : vnEntropy (depolarizingOutput p (1 / 2)) =
    binEntropy2 (1 - p) + p * Real.logb 2 3 := by
  rw [M_eq, vn_unitary U U_unitary, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool,
    Fintype.sum_bool]
  simp only [dd, binEntropy2, binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.logb]
  simp
  have h3 : negMulLog (p / 3) = negMulLog p / 3 + p * (log 3 / 3) := by
    rw [div_eq_mul_inv, negMulLog_mul, negMulLog, negMulLog, Real.log_inv]; ring
  rw [h3]
  ring

theorem main (p q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    referenceFidelity (pauliDepolarizing p) (qBasis 0 q) = 1 - p + (p / 3) * (1 - 2 * q) ^ 2 ∧
    referenceFidelity (pauliDepolarizing p) (qBasis 0 (1 / 2)) = 1 - p ∧
    vnEntropy (depolarizingOutput p (1 / 2)) =
      binEntropy2 (referenceFidelity (pauliDepolarizing p) (qBasis 0 (1 / 2))) +
        (1 - referenceFidelity (pauliDepolarizing p) (qBasis 0 (1 / 2))) * Real.logb 2 3 := by
  have h2 : referenceFidelity (pauliDepolarizing p) (qBasis 0 (1 / 2)) = 1 - p := by
    rw [fid p (1 / 2) (by norm_num) (by norm_num)]; ring
  refine ⟨fid p q hq hq1, h2, ?_⟩
  rw [h2, vn_half]
  ring

end X6P33F

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P33 in
theorem solution (p q : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    referenceFidelity (pauliDepolarizing p) (qBasis 0 q) = 1 - p + (p / 3) * (1 - 2 * q) ^ 2 ∧
    referenceFidelity (pauliDepolarizing p) (qBasis 0 (1 / 2)) = 1 - p ∧
    vnEntropy (depolarizingOutput p (1 / 2)) =
      binEntropy2 (referenceFidelity (pauliDepolarizing p) (qBasis 0 (1 / 2))) +
        (1 - referenceFidelity (pauliDepolarizing p) (qBasis 0 (1 / 2))) * Real.logb 2 3 :=
  X6P33F.main p q hq hq1
