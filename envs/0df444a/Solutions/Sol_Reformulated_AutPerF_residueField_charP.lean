-- Prove2me | solution 1 for Reformulated.AutPerF.residueField_charP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:32:08.165796+00:00
-- url     : https://prove2.me/submissions/c0f0289c-d4fd-4693-9fbd-44ee80fcabe1

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Residue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal IsLocalRing
open Reformulated Reformulated.AutPerF
universe u
variable (p : ℕ) [Fact p.Prime]
variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A]
  [Fact ¬IsUnit (p : A)]
omit [CharZero A]
namespace Reformulated.AutPerF
theorem _root_.solution : CharP (ResidueField A) p :=
  (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
    rw [← map_natCast (residue A), residue_eq_zero_iff]
    exact (Fact.out : ¬IsUnit (p : A)))
end Reformulated.AutPerF
