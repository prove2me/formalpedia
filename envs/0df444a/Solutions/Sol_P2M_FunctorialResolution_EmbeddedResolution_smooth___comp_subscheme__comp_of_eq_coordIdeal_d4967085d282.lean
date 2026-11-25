-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_smooth___comp_subscheme__comp_of_eq_coordIdeal_d4967085d282
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:57:26.936403+00:00
-- url     : https://prove2.me/submissions/bdfc3aba-b05b-42f9-97a2-3db6d5ea0546

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_AffineSpaceSmooth
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_affineSpaceIsSmooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (Z : X.IdealSheafData) {U : X.Opens}
    (hU : IsAffineOpen U) (c : EtaleChart p U m) (S : Finset (Fin m))
    (h : restrictIdeal Z U = c.coordIdeal S) :
    Smooth ((Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p)) := by
  have hsm : Smooth (affineSpaceFinToSpec k (m - S.card)) := affineSpaceIsSmooth ..
  have het : Etale (c.restrictToSubscheme hU Z S h).map :=
    (c.restrictToSubscheme hU Z S h).isEtale
  have hsm2 : Smooth (c.restrictToSubscheme hU Z S h).map := inferInstance
  have hc : (c.restrictToSubscheme hU Z S h).map ≫ affineSpaceFinToSpec k (m - S.card)
      = (Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p) :=
    (c.restrictToSubscheme hU Z S h).comp_struct
  rw [← hc]
  infer_instance
end FunctorialResolution.EmbeddedResolution
