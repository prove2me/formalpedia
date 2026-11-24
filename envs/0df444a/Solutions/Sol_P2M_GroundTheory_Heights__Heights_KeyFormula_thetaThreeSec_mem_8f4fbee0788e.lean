-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThreeSec_mem_8f4fbee0788e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:20.111695+00:00
-- url     : https://prove2.me/submissions/deb509a2-0d5a-4452-aa5f-c8739f48e363

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_differentiable_56fbb8528aea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_add_one_17c6616ebd0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_add_int_mul_I_ff45644aceb5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_intVec_one_081da4c52f7a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Real MeasureTheory intervalIntegral Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution (ν : ℕ) : thetaThreeSec ν ∈ thetaSec tauI (HalfChar.zero 1) 3 := by
  refine ⟨?_, fun v z => ?_, fun u z => ?_⟩
  · intro z
    exact (thetaThree_differentiable ν (z 0)).comp z ((differentiable_apply 0) z)
  · have : perFactor (HalfChar.zero 1) 3 v = 1 := by
      simp [perFactor, HalfChar.a, HalfChar.zero, dotProduct]
    rw [this, one_mul]
    simp only [thetaThreeSec, Pi.add_apply, intVec_one]
    induction (v 0) using Int.induction_on with
    | zero => simp
    | succ k ih => push_cast at ih ⊢; rw [← add_assoc, thetaThree_add_one, ih]
    | pred k ih =>
      push_cast at ih ⊢
      rw [← thetaThree_add_one ν (z 0 + (-(k : ℂ) - 1)),
        show z 0 + (-(k : ℂ) - 1) + 1 = z 0 + -(k : ℂ) by ring, ih]
  · simp only [thetaThreeSec, Pi.add_apply, autFactor, tauI]
    have hτ : ((I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) *ᵥ intVec u) 0 = (u 0 : ℂ) * I := by
      simp [Matrix.mulVec, dotProduct, intVec, mul_comm]
    rw [hτ, thetaThree_add_int_mul_I]
    congr 2
    simp [dotProduct, Matrix.mulVec, intVec, HalfChar.b, HalfChar.zero]
    ring_nf
end GroundTheory.Heights₂.Heights.KeyFormula
