-- Prove2me | solution 1 for Reformulated.AutPerF.wittResidueToRing_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:32:48.905598+00:00
-- url     : https://prove2.me/submissions/51284e76-4afe-4f96-83e5-f9989cfb7786

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
variable [CharP (ResidueField A) p] [PerfectRing (ResidueField A) p]
variable [IsAdicComplete (span {(p : A)}) A]
namespace Reformulated.AutPerF
theorem _root_.solution : Function.Injective (wittResidueToRing p A) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h
  obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' x h
  rw [map_mul, map_pow, map_natCast] at hx
  exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
    ((Units.isUnit b).map (wittResidueToRing p A)).ne_zero hx
end Reformulated.AutPerF
