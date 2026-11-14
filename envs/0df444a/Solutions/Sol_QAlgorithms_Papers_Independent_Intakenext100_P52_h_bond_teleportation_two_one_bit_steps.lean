-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.h_bond_teleportation_two_one_bit_steps
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T04:30:06.711508+00:00
-- url     : https://prove2.me/submissions/eb43df9a-8924-4caa-94c8-b155edb80b9e

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_one_bit_teleportation
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

end QAlgorithms.Papers.Independent.Intakenext100.P52
open QAlgorithms.Papers.Independent.Intakenext100.P52
set_option autoImplicit false
private theorem hBond_apply (a b : Bool) : hBond (a,b) = (1 / 2 : ℂ) * czPhase a b := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  cases a <;> cases b <;>
    norm_num [hBond, czPhase, act, tensorVec, hadamard, ket, controlled, pauliZ,
      Matrix.mulVec, dotProduct, Matrix.one_apply, Fintype.sum_prod_type, Fintype.sum_bool,
      Complex.ofReal_inv, ← pow_two, inv_pow, h2]

set_option maxHeartbeats 1500000

set_option autoImplicit false

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Intakenext100.P52
noncomputable section

open scoped Matrix ComplexConjugate



open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Common one-bit primitive, PDF p.16. Printed CZ basis list swaps its last
two ray labels: corrected I,X,Z,XZ labels are ++,+-,-+,--, up to phase.
The H-bond teleportation instrument equals the two sequential CZ/X steps. -/
theorem solution :
    Orthonormal ℂ (fun p : QubitPair => hBell p.1 p.2) ∧
    (∀ c d : Bool, pureDensity (act (controlled pauliZ) (hBell c d)) =
      pureDensity (tensorVec (equatorial 0 c) (equatorial 0 d))) ∧
    (∀ (psi : Vec Bool), IsState psi → ∀ c d : Bool,
      let v := teleportContraction psi hBond (hBell c d)
      pureDensity v = pureDensity (lineBranch 2 (fun _ => 0) ![c,d] psi) ∧
      pureDensity v = (1 / 4 : ℝ) • pureDensity (act (pauliByproduct d c) psi) ∧
      ‖v‖ ^ 2 = (1 / 4 : ℝ)) := by
  have hB (c d i j : Bool) : hBell c d (i,j) = (1/2 : ℂ) *
      (if c && xor i d then -1 else 1) * czPhase (xor i d) j := by
    cases c <;> cases d <;> cases i <;> cases j <;>
      norm_num [hBell, hBond_apply, czPhase, act, pauliByproduct, pauliX, pauliZ,
        Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.one_apply,
        Fintype.sum_prod_type, Fintype.sum_bool]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro ⟨a,b⟩ ⟨c,d⟩
    simp only [PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply]
    cases a <;> cases b <;> cases c <;> cases d <;>
      norm_num [hB, czPhase, Fintype.sum_bool, Complex.conj_ofNat]
  · intro c d
    have hv : act (controlled pauliZ) (hBell c d) =
        (if c && d then (-1 : ℂ) else 1) •
          tensorVec (equatorial 0 c) (equatorial 0 d) := by
      ext ⟨a,b⟩
      cases c <;> cases d <;> cases a <;> cases b <;>
        norm_num [act, hB, controlled, pauliZ, czPhase, tensorVec, equatorial,
          Matrix.mulVec, dotProduct, Matrix.one_apply, Fintype.sum_prod_type,
          Fintype.sum_bool, Complex.ofReal_inv, ← pow_two, inv_pow, h2] <;> ring
    rw [hv]
    cases c <;> cases d <;> ext i j <;>
      norm_num [pureDensity, PiLp.smul_apply, map_mul] <;> ring
  · intro psi hpsi c d
    dsimp only
    have hb : teleportContraction psi hBond (hBell c d) =
        (if c && d then (-1/2 : ℂ) else (1/2 : ℂ)) • act (pauliByproduct d c) psi := by
      ext b
      cases c <;> cases d <;> cases b <;>
        norm_num [teleportContraction, hBell, hBond_apply, czPhase, act,
          pauliByproduct, pauliX, pauliZ, Matrix.mul_apply, Matrix.mulVec,
          dotProduct, Matrix.kronecker, Matrix.one_apply, Fintype.sum_prod_type,
          Fintype.sum_bool] <;> norm_num [Complex.conj_ofNat] <;> ring
    have hD : pureDensity (teleportContraction psi hBond (hBell c d)) =
        (1 / 4 : ℝ) • pureDensity (act (pauliByproduct d c) psi) := by
      rw [hb]
      cases c <;> cases d <;> ext i j <;>
        norm_num [pureDensity, PiLp.smul_apply, map_mul, Complex.conj_ofNat] <;> ring
    refine ⟨?_, hD, ?_⟩
    · rw [(one_bit_teleportation psi hpsi).2.2 ![c,d]]
      rw [hD]
      ext i j
      norm_num [pureDensity, PiLp.smul_apply, map_mul, Complex.conj_ofNat]
      ring
    · rw [hb, norm_smul, act_norm_unitary _ (pauliByproduct_unitary d c),
        show ‖psi‖ = 1 from hpsi]
      cases c <;> cases d <;> norm_num