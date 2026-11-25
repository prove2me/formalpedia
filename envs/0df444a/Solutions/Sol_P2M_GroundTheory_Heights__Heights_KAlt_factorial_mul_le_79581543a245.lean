-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_factorial_mul_le_79581543a245
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:00:13.454605+00:00
-- url     : https://prove2.me/submissions/aa8194ab-ab99-4fb4-bb44-117de68111ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltFrob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Finset
open GroundTheory.Heights₂.Heights.KAlt
namespace GroundTheory.Heights₂.Heights.KAlt
theorem _root_.solution (s c d : ℕ) :
    (s + c).factorial * (c + d).factorial ≤ (s + c + d).factorial * c.factorial := by
  induction d with
  | zero => simp [mul_comm]
  | succ d ih =>
    rw [show c + (d + 1) = (c + d) + 1 by ring, Nat.factorial_succ,
      show s + c + (d + 1) = (s + c + d) + 1 by ring, Nat.factorial_succ]
    calc (s + c).factorial * ((c + d + 1) * (c + d).factorial)
        = (c + d + 1) * ((s + c).factorial * (c + d).factorial) := by ring
      _ ≤ (s + c + d + 1) * ((s + c + d).factorial * c.factorial) :=
          Nat.mul_le_mul (by omega) ih
      _ = ((s + c + d + 1) * (s + c + d).factorial) * c.factorial := by ring
end GroundTheory.Heights₂.Heights.KAlt
