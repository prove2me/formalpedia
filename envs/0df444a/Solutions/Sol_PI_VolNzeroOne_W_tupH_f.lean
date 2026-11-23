-- Prove2me | solution 1 for PI.VolNzeroOne.W.tupH_f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:56.771212+00:00
-- url     : https://prove2.me/submissions/cccf5e5e-f229-452b-a6fd-9a6500c4287e

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
theorem _root_.solution {M r : ℕ} (P : Frame E M r) (a : Fin r) : tupH P (Fin.natAdd (r + 1) a) = P.f a := by
  simp [tupH]
end PI.VolNzeroOne.W
