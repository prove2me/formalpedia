-- Prove2me | solution 1 for PI.VolNzeroOne.W.if_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:48:56.407414+00:00
-- url     : https://prove2.me/submissions/f753a5d4-d74b-4981-9cfc-53b04d674942

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
theorem _root_.solution {r : ℕ} {a b : Fin r}
    (h : (Fin.natAdd (r + 1) a : Fin (r + 1 + r)) = Fin.natAdd (r + 1) b) : a = b := by
  have h' := congrArg Fin.val h
  simp at h'
  exact Fin.ext h'
end PI.VolNzeroOne.W
