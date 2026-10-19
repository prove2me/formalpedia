-- Prove2me | solution 1 for PermanentRollout.CircuitPrefix.values_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/c9e12377-de9f-40c3-846f-7a462a66096a

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_forwardFold_size
import Theorems.Thm_PermanentRollout_CircuitPrefix_forwardFold_size

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
open PermanentRollout.CircuitPrefix
namespace PermanentRollout.CircuitPrefix
theorem _root_.solution {ι : Type} (state : CircuitPrefix ι) :
    state.values.size = state.program.length := by
  simpa [values] using
    forwardFold_size state.program (#[] : Array (MvPolynomial ι ℂ))
end PermanentRollout.CircuitPrefix
