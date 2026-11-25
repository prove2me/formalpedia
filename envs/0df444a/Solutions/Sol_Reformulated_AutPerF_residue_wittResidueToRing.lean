-- Prove2me | solution 1 for Reformulated.AutPerF.residue_wittResidueToRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:12:02.016833+00:00
-- url     : https://prove2.me/submissions/bbbb87fc-8834-465a-8ddd-a1c84c5cbc47

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Residue
import Theorems.Thm_Reformulated_AutPerF_modPToResidue_residueSection
import Theorems.Thm_Reformulated_AutPerF_Tilt_coeff_ofPerfect


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
theorem _root_.solution (x : WittVector p (ResidueField A)) :
    residue A (wittResidueToRing p A x) = x.coeff 0 := by
  rw [← modPToResidue_mk p, wittResidueToRing, RingHom.comp_apply, Ainf.theta,
    WittVector.mk_fontaineTheta, Ainf.ofWitt, WittVector.map_coeff, Tilt.coeff_ofPerfect]
  exact modPToResidue_residueSection p A _
end Reformulated.AutPerF
