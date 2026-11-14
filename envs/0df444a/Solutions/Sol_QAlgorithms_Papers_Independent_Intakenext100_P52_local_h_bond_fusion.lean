-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.local_h_bond_fusion
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T04:03:09.806076+00:00
-- url     : https://prove2.me/submissions/a5385766-e63b-4322-88a1-efff6f23682c

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52
import Mathlib.Analysis.InnerProductSpace.LinearMap

noncomputable section
open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P21
namespace QAlgorithms.Papers.Independent.Intakenext100.P52

private theorem act_inner_unitary {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (x y : Vec I) :
    inner ℂ (act U x) (act U y) = inner ℂ x y := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, act]
  rw [dotProduct_comm (U.mulVec (WithLp.ofLp y)), dotProduct_comm (WithLp.ofLp y)]
  change star (U.mulVec (WithLp.ofLp x)) ⬝ᵥ (U.mulVec (WithLp.ofLp y)) = _
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  have h : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff'.mp hU)
  rw [h, Matrix.vecMul_one]

private theorem act_norm_unitary {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (x : Vec I) :
    ‖act U x‖ = ‖x‖ := by
  exact (LinearMap.norm_map_iff_inner_map_map (Matrix.toEuclideanLin U)).mpr
    (act_inner_unitary U hU) x

private theorem pauliByproduct_unitary (x z : Bool) :
    pauliByproduct x z ∈ Matrix.unitaryGroup Bool ℂ := by
  cases x <;> cases z <;> apply Matrix.mem_unitaryGroup_iff.mpr <;>
    ext i j <;> cases i <;> cases j <;>
    norm_num [pauliByproduct, pauliX, pauliZ, Matrix.mul_apply, Fintype.sum_bool,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

private theorem act_mul {I : Type*} [Fintype I] (A B : Matrix I I ℂ) (x : Vec I) :
    act (A * B) x = act A (act B x) := by
  exact congrArg (WithLp.toLp 2) (Matrix.mulVec_mulVec x.ofLp A B).symm

private theorem rotatedBell_eq (U : Matrix Bool Bool ℂ) (c d : Bool) :
    rotatedBell U c d = rotatedEntangledKet (pauliByproduct d c * U) := by
  have hP : (pauliByproduct d c)ᴴ = pauliZ ^ c.toNat * pauliX ^ d.toNat := by
    cases c <;> cases d <;> ext i j <;> cases i <;> cases j <;>
      norm_num [pauliByproduct, pauliX, pauliZ, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fintype.sum_bool]
  simp only [rotatedBell, sourceBellBasis, rotatedEntangledKet, Matrix.conjTranspose_mul, hP]
  rw [← act_mul]
  congr 1
  simpa using (Matrix.mul_kronecker_mul Uᴴ (pauliZ ^ c.toNat * pauliX ^ d.toNat)
    (1 : Matrix Bool Bool ℂ) (1 : Matrix Bool Bool ℂ)).symm

private theorem sourceBellBasis_orthonormal :
    Orthonormal ℂ (fun p : QubitPair => sourceBellBasis p.1 p.2) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [orthonormal_iff_ite]
  intro ⟨c,d⟩ ⟨e,f⟩
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply]
  cases c <;> cases d <;> cases e <;> cases f <;>
    norm_num [sourceBellBasis, act, finiteMaxEntangled, pauliX, pauliZ,
      PiLp.toLp_apply, Matrix.kronecker_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fintype.sum_prod_type, Fintype.sum_bool, Matrix.one_apply,
      Complex.ofReal_inv, ← pow_two, inv_pow, h2]
end QAlgorithms.Papers.Independent.Intakenext100.P52
namespace QAlgorithms.Papers.Independent.Intakenext100.P52

private theorem cz_unitary : controlled pauliZ ∈ Matrix.unitaryGroup QubitPair ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  ext ⟨a,b⟩ ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [controlled, pauliZ, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool]

private theorem pauli_trace (a b : QubitPair) :
    (pauliByproduct a.1 a.2 * (pauliByproduct b.1 b.2)ᴴ).trace =
      if a = b then (2 : ℂ) else 0 := by
  rcases a with ⟨x1,x2⟩; rcases b with ⟨y1,y2⟩
  cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;>
    norm_num [pauliByproduct, pauliX, pauliZ, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_bool]

private theorem czTeleportGate_unitary (a b : QubitPair) :
    czTeleportGate a b ∈ Matrix.unitaryGroup QubitPair ℂ := by
  exact (Matrix.unitaryGroup QubitPair ℂ).mul_mem
    (Matrix.kronecker_mem_unitary (pauliByproduct_unitary a.1 a.2)
      (pauliByproduct_unitary b.1 b.2)) cz_unitary

private theorem czTeleportGate_trace (a b : QubitPair × QubitPair) :
    (czTeleportGate a.1 a.2 * (czTeleportGate b.1 b.2)ᴴ).trace =
      if a = b then (4 : ℂ) else 0 := by
  have hCZ : controlled pauliZ * (controlled pauliZ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp cz_unitary
  simp only [czTeleportGate, Matrix.conjTranspose_mul]
  rw [← mul_assoc, mul_assoc (Matrix.kronecker _ _), hCZ, mul_one]
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker]
  have hK := Matrix.mul_kronecker_mul (pauliByproduct a.1.1 a.1.2)
    (pauliByproduct b.1.1 b.1.2)ᴴ (pauliByproduct a.2.1 a.2.2)
    (pauliByproduct b.2.1 b.2.2)ᴴ
  rw [← hK, Matrix.trace_kronecker, pauli_trace, pauli_trace]
  rcases a with ⟨x1,x2⟩; rcases b with ⟨y1,y2⟩
  by_cases h1 : x1 = y1 <;> by_cases h2 : x2 = y2 <;> norm_num [h1,h2]
end QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Intakenext100.P52
noncomputable section

open scoped Matrix ComplexConjugate



open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Fig.14, PDF pp.17–18: exact coefficient 1/2 before normalization. -/
theorem solution (psi1 psi2 : Vec Bool)
    (hpsi1 : IsState psi1) (hpsi2 : IsState psi2) :
    let v := applyRect (Matrix.kronecker fuse fuse) (fusionResource psi1 psi2)
    v = (1 / 2 : ℂ) • act (controlled pauliZ) (tensorVec psi1 psi2) ∧
    ‖v‖ = (1 / 2 : ℝ) ∧
    (2 : ℂ) • v = act (controlled pauliZ) (tensorVec psi1 psi2) := by
  dsimp only
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hb : applyRect (Matrix.kronecker fuse fuse) (fusionResource psi1 psi2) =
      (1 / 2 : ℂ) • act (controlled pauliZ) (tensorVec psi1 psi2) := by
    ext ⟨a,b⟩
    cases a <;> cases b <;>
      norm_num [applyRect, fusionResource, fuse, hBond, act, tensorVec, hadamard,
        ket, controlled, pauliZ, Matrix.kronecker, Matrix.mulVec, dotProduct,
        Matrix.one_apply, Fintype.sum_prod_type, Fintype.sum_bool,
        Complex.ofReal_inv, ← pow_two, inv_pow, h2] <;> ring
  have ht : ‖tensorVec psi1 psi2‖ = 1 := by
    have hs : ‖tensorVec psi1 psi2‖ ^ 2 = ‖psi1‖ ^ 2 * ‖psi2‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, tensorVec, Fintype.sum_prod_type,
        PiLp.toLp_apply, norm_mul, mul_pow, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [show ‖psi1‖ = 1 from hpsi1, show ‖psi2‖ = 1 from hpsi2] at hs
    nlinarith [norm_nonneg (tensorVec psi1 psi2)]
  refine ⟨hb, ?_, ?_⟩
  · rw [hb, norm_smul, act_norm_unitary _ cz_unitary, ht]
    norm_num
  · rw [hb, smul_smul]
    norm_num