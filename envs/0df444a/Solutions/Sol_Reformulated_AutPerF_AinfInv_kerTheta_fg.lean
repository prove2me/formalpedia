-- Prove2me | solution 1 for Reformulated.AutPerF.AinfInv.kerTheta_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:29:07.022637+00:00
-- url     : https://prove2.me/submissions/92c73979-1c18-4a96-90a4-f0c5c38ce8fe

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_AinfInv_kerTheta_eq

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
open Reformulated.AutPerF.AinfInv
variable [IsDomain R]
variable [ValuationRing R]
variable [CharZero R]
namespace Reformulated.AutPerF.AinfInv
theorem _root_.solution [IsAlgClosed (FractionRing R)] : (kerTheta p R).FG := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  rw [kerTheta_eq ϖ]
  exact Submodule.fg_span_singleton _
end Reformulated.AutPerF.AinfInv
