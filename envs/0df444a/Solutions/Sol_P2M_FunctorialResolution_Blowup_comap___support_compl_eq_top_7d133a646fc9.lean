-- Prove2me | solution 1 for P2M_FunctorialResolution_Blowup_comap___support_compl_eq_top_7d133a646fc9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:15.63989+00:00
-- url     : https://prove2.me/submissions/a38c9337-762b-4233-b1a1-0c39d3da4c3d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Theorems.Thm_FunctorialResolution_Blowup_comap_eq_top_of_notMem_support


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
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
theorem _root_.solution {X : Scheme.{u}} (Z : X.IdealSheafData) :
    Z.comap (Scheme.Opens.ι Z.support.compl) = ⊤ := by
  refine comap_eq_top_of_notMem_support _ Z fun x => ?_
  show x.1 ∉ Z.support
  exact x.2
end FunctorialResolution.Blowup
