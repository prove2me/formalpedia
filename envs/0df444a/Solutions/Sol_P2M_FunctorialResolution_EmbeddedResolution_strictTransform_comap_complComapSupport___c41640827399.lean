-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_strictTransform_comap_complComapSupport___c41640827399
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:15.525984+00:00
-- url     : https://prove2.me/submissions/ca9ccb24-75f9-44fe-9ea1-9902f69fd68b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransformOffCenter
import Theorems.Thm_P2M_FunctorialResolution_Blowup_comap_ker_subscheme__comp_0b937eab6fcc
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_comap_ker_subscheme__comp_6d441ab4fd0b
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_ker___preimage_comp_subscheme__eq_ker_comap_1c8ee5f81d10


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X X₁ : Scheme.{u}} [IsNoetherian X₁]
    (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    (Blowup.strictTransform π Z D).comap (Scheme.Opens.ι (complComapSupport π Z)) =
      (D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z)) := by
  have hqι : QuasiCompact (Scheme.Opens.ι (complComapSupport π Z)) := inferInstance
  have hq1 : QuasiCompact
      (((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι) := inferInstance
  have hq2 : QuasiCompact
      ((((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι) ≫
        Scheme.Opens.ι (complComapSupport π Z)) := inferInstance
  have h1 : Blowup.strictTransform π Z D =
      ((((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι) ≫
        Scheme.Opens.ι (complComapSupport π Z)).ker :=
    ker_ι_preimage_comp_subschemeι_eq_ker_comap (D.comap π) (complComapSupport π Z)
  rw [h1]
  exact comap_ker_subschemeι_comp
    ((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z)))
    (Scheme.Opens.ι (complComapSupport π Z))
end FunctorialResolution.EmbeddedResolution
