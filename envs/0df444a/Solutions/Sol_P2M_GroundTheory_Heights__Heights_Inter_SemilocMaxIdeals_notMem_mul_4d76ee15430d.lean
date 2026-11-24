-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_notMem_mul_4d76ee15430d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:48.657261+00:00
-- url     : https://prove2.me/submissions/98c35d81-b27e-42b9-bb7b-2582b2b23522

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFibreOverFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocMaxIdeals

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
open regularityLocalFlat_holds
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (P : Ideal (MRing ι)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι)))
namespace GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
theorem _root_.solution {I : Ideal (MRing ι)} (hI : I.IsPrime) {a b : MRing ι} (ha : a ∉ I) (hb : b ∉ I) :
    a * b ∉ I :=
  fun h => (hI.mem_or_mem h).elim ha hb
end GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
