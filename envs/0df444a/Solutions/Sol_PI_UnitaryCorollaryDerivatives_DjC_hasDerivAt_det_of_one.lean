-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.hasDerivAt_det_of_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:01.741872+00:00
-- url     : https://prove2.me/submissions/7443ea94-d4b4-41c1-a238-b44b7ac7431c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumEqSumCompEmbedding
import Definitions.Def_Lemmata_B110_ExistsMoved
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Theorems.Thm_Bl_b110_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.DjC
variable {n : Type} [Fintype n] [DecidableEq n]
namespace PI.UnitaryCorollaryDerivatives.DjC
theorem _root_.solution (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 := by
  first | exact Bl.b110.goal1 .. | (apply Bl.b110.goal1 <;> assumption) | (intros; apply Bl.b110.goal1 <;> assumption) | (apply @Bl.b110.goal1 <;> assumption) | (intros; apply @Bl.b110.goal1 <;> assumption) | (apply @Bl.b110.goal1 <;> first | assumption | infer_instance) | exact @Bl.b110.goal1 n ‹_› ‹_› A A' h0 h | exact @Bl.b110.goal1 n ‹_› ‹_› A A' h0 | exact @Bl.b110.goal1 n ‹_› ‹_› A A' | exact @Bl.b110.goal1 n ‹_› ‹_› A | exact @Bl.b110.goal1 n ‹_› ‹_› | exact @Bl.b110.goal1 n ‹_› | exact @Bl.b110.goal1 n
end PI.UnitaryCorollaryDerivatives.DjC
