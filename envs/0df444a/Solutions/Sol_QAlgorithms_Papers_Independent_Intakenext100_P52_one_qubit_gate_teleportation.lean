-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.one_qubit_gate_teleportation
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T03:57:08.668182+00:00
-- url     : https://prove2.me/submissions/b6c3ba4d-b4cf-485d-ae2b-174f4f93bfcf

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_rotated_entangled_contraction
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

open QAlgorithms.Papers.Independent.Intakenext100.P52
noncomputable section

open scoped Matrix ComplexConjugate



open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Rotated Bell gate teleportation, PDF pp.2–4, including U=I as Fig.1.
All four measured kets are orthonormal; branches retain their coefficient 1/2. -/
theorem solution (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    Orthonormal ℂ (fun p : QubitPair => rotatedBell U p.1 p.2) ∧
    ∀ (psi : Vec Bool), IsState psi → ∀ c d : Bool,
      let b := teleportContraction psi (finiteMaxEntangled Bool) (rotatedBell U c d)
      b = (1 / 2 : ℂ) • act (pauliByproduct d c * U) psi ∧
      ‖b‖ ^ 2 = (1 / 4 : ℝ) ∧ (2 : ℂ) • b = act (pauliByproduct d c * U) psi := by
  have hK : Matrix.kronecker Uᴴ (1 : Matrix Bool Bool ℂ) ∈ Matrix.unitaryGroup QubitPair ℂ :=
    Matrix.kronecker_mem_unitary (Unitary.star_mem hU) (Matrix.unitaryGroup Bool ℂ).one_mem
  constructor
  · rw [orthonormal_iff_ite]
    intro p q
    change inner ℂ (act (Matrix.kronecker Uᴴ 1) (sourceBellBasis p.1 p.2))
      (act (Matrix.kronecker Uᴴ 1) (sourceBellBasis q.1 q.2)) = _
    rw [act_inner_unitary _ hK]
    exact (orthonormal_iff_ite.mp sourceBellBasis_orthonormal) p q
  · intro psi hpsi c d
    dsimp only
    have hP := pauliByproduct_unitary d c
    have hPU := (Matrix.unitaryGroup Bool ℂ).mul_mem hP hU
    have hb : teleportContraction psi (finiteMaxEntangled Bool) (rotatedBell U c d) =
        (1 / 2 : ℂ) • act (pauliByproduct d c * U) psi := by
      rw [rotatedBell_eq]
      simpa using rotated_entangled_contraction _ hPU psi hpsi
    refine ⟨hb, ?_, ?_⟩
    · rw [hb, norm_smul, act_norm_unitary _ hPU]
      rw [show ‖psi‖ = 1 from hpsi]
      norm_num
    · rw [hb, smul_smul]
      norm_num