-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.map_liftWitt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:08:10.303892+00:00
-- url     : https://prove2.me/submissions/e636c71f-e6a3-4388-9d1d-edfd31daea89

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Theorems.Thm_Reformulated_AutPerF_Ainf_map_ofWitt

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
variable {p}
namespace Reformulated.AutPerF
namespace Ainf
theorem _root_.solution (e : R →+* S) (g : WittVector p k →+* R) (x : WittVector p k) :
    Ainf.map p e (Ainf.liftWitt p g x) = Ainf.liftWitt p (e.comp g) x := by
  rw [Ainf.liftWitt, Ainf.map_ofWitt, Ainf.liftWitt]
  congr 2
end Ainf
end Reformulated.AutPerF
