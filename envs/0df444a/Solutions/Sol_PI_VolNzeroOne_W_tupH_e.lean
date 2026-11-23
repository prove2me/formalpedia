-- Prove2me | solution 1 for PI.VolNzeroOne.W.tupH_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:44.6944+00:00
-- url     : https://prove2.me/submissions/ca087b35-96cb-44cb-aa1c-e75776ed9ccd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolNzeroOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NilpotentVolumeOne_LinearIndependentFrameWithNormal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolNzeroOne PI.VolNzeroOne.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace PI.VolNzeroOne.W
theorem _root_.solution {M r : ℕ} (P : Frame E M r) (a : Fin r) :
    tupH P (Fin.castAdd r (Fin.castSucc a)) = P.e a := by
  simp [tupH, F0]
end PI.VolNzeroOne.W
