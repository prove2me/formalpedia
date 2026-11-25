-- Prove2me | solution 1 for P2M_FunctorialResolution_Blowup_affineBlowupChart_eq_away__6f5d034cade6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:49:07.0548+00:00
-- url     : https://prove2.me/submissions/f559f3d3-9d2b-4a82-a1af-fec6d2f9056e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Theorems.Thm_FunctorialResolution_Blowup_reesGenerator_mem_reesGrading


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]
namespace FunctorialResolution.Blowup
theorem _root_.solution (I : Ideal R) (a : ↥I) :
    affineBlowupChart I a =
      AlgebraicGeometry.Proj.awayι (reesGrading I) (reesGenerator I a) (reesGenerator_mem_reesGrading I a)
        Nat.one_pos := rfl
end FunctorialResolution.Blowup
