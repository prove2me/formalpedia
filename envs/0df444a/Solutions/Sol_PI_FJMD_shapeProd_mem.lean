-- Prove2me | solution 1 for PI.FJMD.shapeProd_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:47.785909+00:00
-- url     : https://prove2.me/submissions/c84ba1ba-e19c-4623-92ee-367261fcbc53

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Theorems.Thm_PI_FJMD_det_mem_subalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.FJMD
open PI.FJM
namespace PI.FJMD
theorem _root_.solution {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A)
    {m k : ℕ} (M : Matrix (Fin m) (Fin k) A) (α : List ℕ)
    (h : ∀ (i : Fin m) (j : Fin k), i.val < α.length → j.val < α.length → M i j ∈ S) :
    shapeProd M α ∈ S := by
  unfold PI.FJM.shapeProd
  refine prod_mem fun t ht => pow_mem ?_ _
  have ht' : t < α.length := Finset.mem_range.mp ht
  unfold PI.FJM.leadT
  split_ifs with hc
  · apply det_mem_subalgebra S
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    rw [Matrix.submatrix_apply]
    exact h _ _ (show i.val < α.length by omega) (show j.val < α.length by omega)
  · exact zero_mem _
end PI.FJMD
