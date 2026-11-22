-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.theta_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:44.862806+00:00
-- url     : https://prove2.me/submissions/dce4c276-422b-412f-ba7a-f42769341a01

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel

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
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Ainf
variable [IsDomain R]
variable [ValuationRing R]
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution [IsAlgClosed (FractionRing R)] : Function.Surjective (theta p R) := by
  intro a
  obtain ⟨x, hx⟩ := Tilt.untilt_surjective (p := p) a
  exact ⟨teich p x, by rw [theta_teich, hx]⟩
end Reformulated.AutPerF.Ainf
