-- Prove2me | solution 1 for PI.VolNzeroOne.W.if_ne_ie
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:34.804801+00:00
-- url     : https://prove2.me/submissions/fc9c45bf-e242-4afe-9e15-fa50bbc4d85e

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
theorem _root_.solution {r : ℕ} (a b : Fin r) :
    (Fin.natAdd (r + 1) a : Fin (r + 1 + r)) ≠ Fin.castAdd r (Fin.castSucc b) := by
  intro h
  have h' := congrArg Fin.val h
  simp at h'
  omega
end PI.VolNzeroOne.W
