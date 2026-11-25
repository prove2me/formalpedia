-- Prove2me | solution 1 for Reformulated.AutPerF.Tilt.mk_seq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:37:43.864793+00:00
-- url     : https://prove2.me/submissions/562761ec-83f4-4397-bcd5-02eec3144516

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_MapEqPadicPowCyclotomicCharacter
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap



set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u v
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
open Reformulated.AutPerF.Tilt
namespace Reformulated.AutPerF.Tilt
theorem _root_.solution (y : Tilt p R) (n : ℕ) :
    Ideal.Quotient.mk (span {(p : R)}) (seq n y) = PreTilt.coeff n y := by
  obtain ⟨z, rfl⟩ := (seqEquiv p R).surjective y
  simp only [seq, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rfl
end Reformulated.AutPerF.Tilt
