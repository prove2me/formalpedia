-- Prove2me | solution 1 for PI.FJMD.hwVec_mem_supported
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:25.041411+00:00
-- url     : https://prove2.me/submissions/fe10e7f0-aca3-4098-9b48-57ee75d5f450

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Theorems.Thm_PI_FJMD_shapeProd_mem
import Theorems.Thm_PI_FJMD_posPart_length
import Theorems.Thm_PI_FJMD_negPart_length
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
private theorem fin_rev_val {n : ℕ} (i : Fin n) : (Fin.rev i).val = n - (i.val + 1) := rfl
private theorem varMat_apply_mem_supported {p q r s m k : ℕ} (ρ : Fin m → FockH1Action.Ix p q)
    (κ : Fin k → FockH1Action.Ix r s) (T : Set (FockH1Action.Ln p q r s)) (i : Fin m) (j : Fin k)
    (h : (ρ i, κ j) ∈ T) : PI.FJM.varMat ρ κ i j ∈ MvPolynomial.supported ℂ T := by
  rw [show PI.FJM.varMat ρ κ i j = MvPolynomial.X (ρ i, κ j) from rfl]
  first
  | exact MvPolynomial.X_mem_supported.mpr h
  | exact MvPolynomial.mem_supported.mpr (by rw [MvPolynomial.vars_X]; simpa using h)
end PI.FJMD
end
end

set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.FJMD
open PI.FJM
namespace PI.FJMD
theorem _root_.solution (p q r s : ℕ) (a b c d : List ℤ) :
    hwVec p q r s a b c d ∈ MvPolynomial.supported ℂ
      {l : Ln p q r s | inS a.length b.length c.length d.length l} := by
  unfold PI.FJM.hwVec
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_
  · apply shapeProd_mem
    intro i j hi hj
    rw [posPart_length] at hi hj
    apply varMat_apply_mem_supported
    simp only [Set.mem_setOf_eq, inS]
    exact ⟨hi, hj⟩
  · apply shapeProd_mem
    intro i j hi hj
    rw [negPart_length] at hi hj
    apply varMat_apply_mem_supported
    simp only [Set.mem_setOf_eq, inS, fin_rev_val]
    have := i.isLt
    have := j.isLt
    constructor <;> omega
  · apply shapeProd_mem
    intro i j hi hj
    rw [posPart_length] at hi hj
    apply varMat_apply_mem_supported
    simp only [Set.mem_setOf_eq, inS]
    exact ⟨hi, hj⟩
  · apply shapeProd_mem
    intro i j hi hj
    rw [negPart_length] at hi hj
    apply varMat_apply_mem_supported
    simp only [Set.mem_setOf_eq, inS, fin_rev_val]
    have := i.isLt
    have := j.isLt
    constructor <;> omega
end PI.FJMD
