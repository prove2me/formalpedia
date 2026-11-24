-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_sumAlgEquiv_rename_inr_97418c89fc9c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:34.884744+00:00
-- url     : https://prove2.me/submissions/feab8309-6455-4284-85e8-223e8dee227a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {S : Type} [Fintype S]
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype S]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (f : MRing ι) :
    sumAlgEquiv ℤ S (Σ k, ι k) (rename Sum.inr f) = C f := by
  have := AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr ℤ S (Σ k, ι k)) f
  simpa [algebraMap_eq] using this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
