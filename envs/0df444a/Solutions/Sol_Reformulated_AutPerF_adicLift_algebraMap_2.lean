-- Prove2me | solution 2 for Reformulated.AutPerF.adicLift_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:31:26.71237+00:00
-- url     : https://prove2.me/submissions/ac664865-d73b-42cd-a150-b0c1a26a34f7

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
variable {A Q : Type*} [CommRing A] [CommRing Q]
namespace Reformulated.AutPerF
theorem _root_.solution (p : ℕ) [IsAdicComplete (span {(p : Q)}) Q] (g : A →+* Q) (a : A) :
    adicLift p g (algebraMap A _ a) = g a := by
  change (AdicCompletion.ofAlgEquiv (span {(p : Q)})).symm (adicMap _ _ g _ _) = _
  rw [adicMap_algebraMap, AlgEquiv.commutes]; rfl
end Reformulated.AutPerF
