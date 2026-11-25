-- Prove2me | solution 1 for Reformulated.AutPerF.wittResidueMap_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:58:39.631298+00:00
-- url     : https://prove2.me/submissions/254eda64-a40e-478e-8324-6ad89a1ae177

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section

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
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]
variable {k : Type w} [CommRing k] [CharP k p] [PerfectRing k p]
omit [Fact ¬IsUnit (p : R)]
variable {p}
namespace Reformulated.AutPerF
theorem _root_.solution (g : WittVector p k →+* R) (x : WittVector p k) :
    wittResidueMap p g (x.coeff 0) = Ideal.Quotient.mk _ (g x) := by
  have : (WittVector.quotientPEquiv (p := p) (k := k)).symm (x.coeff 0) =
      Ideal.Quotient.mk _ x := by
    rw [RingEquiv.symm_apply_eq]; rfl
  change Ideal.quotientMap _ g (span_natCast_le_comap p g) ((WittVector.quotientPEquiv (p := p) (k := k)).symm _) = _
  rw [this, Ideal.quotientMap_mk]
end Reformulated.AutPerF
