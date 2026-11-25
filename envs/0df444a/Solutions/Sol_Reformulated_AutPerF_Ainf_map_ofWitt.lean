-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.map_ofWitt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:57:58.354016+00:00
-- url     : https://prove2.me/submissions/90dda257-9d00-4f26-aea3-baa8709c2a73

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Theorems.Thm_Reformulated_AutPerF_Tilt_map_ofPerfect
import Theorems.Thm_Reformulated_AutPerF_Ainf_ofWitt_teichmuller
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


attribute [local simp] Reformulated.AutPerF.Ainf.ofWitt_teichmuller

set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]
variable {k : Type w} [CommRing k] [CharP k p] [PerfectRing k p]
variable {p}
namespace Reformulated.AutPerF
namespace Ainf
theorem _root_.solution (e : R →+* S) (f : k →+* R ⧸ span {(p : R)}) (x : WittVector p k) :
    Ainf.map p e (Ainf.ofWitt p f x) =
      Ainf.ofWitt p ((Ideal.quotientMap _ e (span_natCast_le_comap p e)).comp f) x := by
  ext n
  simp [Ainf.ofWitt, Ainf.map, Tilt.map_ofPerfect]
end Ainf
end Reformulated.AutPerF
