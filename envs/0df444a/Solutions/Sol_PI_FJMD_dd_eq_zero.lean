-- Prove2me | solution 1 for PI.FJMD.dd_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:35.041015+00:00
-- url     : https://prove2.me/submissions/1c4db02a-cff3-4caa-a80c-668315c43591

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix FockH1Action
namespace PI.FJMD
open PI.FJM
private theorem pderiv_pderiv_comm_of_complex {σ : Type*} (i j : σ) (P : MvPolynomial σ ℂ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on
  next a =>
    simp only [MvPolynomial.pderiv_C, map_zero]
  next P Q hP hQ =>
    simp only [map_add, hP, hQ]
  next P n hP =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul, MvPolynomial.pderiv_X, Pi.single_apply]
    split_ifs <;>
      simp only [Derivation.map_one_eq_zero, map_zero, mul_zero, zero_mul, add_zero, zero_add,
        mul_one, one_mul, hP] <;> ring
private theorem pderiv_eq_zero_of_mem_supported_of_not_mem {σ : Type*} {S : Set σ} {P : MvPolynomial σ ℂ}
    (hP : P ∈ MvPolynomial.supported ℂ S) {i : σ} (hi : i ∉ S) : MvPolynomial.pderiv i P = 0 := by
  have hv : i ∉ P.vars := fun hmem => hi ((MvPolynomial.mem_supported.mp hP) (Finset.mem_coe.mpr hmem))
  first
  | exact MvPolynomial.pderiv_eq_zero_of_notMem_vars hv
  | exact MvPolynomial.pderiv_eq_zero_of_not_mem_vars hv
end PI.FJMD
end
end

set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.FJMD
open PI.FJM
namespace PI.FJMD
theorem _root_.solution {p q r s : ℕ} {S : Set (Ln p q r s)} {P : Pol p q r s}
    (hP : P ∈ MvPolynomial.supported ℂ S) {l l' : Ln p q r s} (h : l ∉ S ∨ l' ∉ S) : dd l l' P = 0 := by
  have key : PI.FJM.dd l l' P = MvPolynomial.pderiv l (MvPolynomial.pderiv l' P) := by
    first
    | rfl
    | simp [PI.FJM.dd]
  rw [key]
  rcases h with h | h
  · rw [pderiv_pderiv_comm_of_complex, pderiv_eq_zero_of_mem_supported_of_not_mem hP h, map_zero]
  · rw [pderiv_eq_zero_of_mem_supported_of_not_mem hP h, map_zero]
end PI.FJMD
