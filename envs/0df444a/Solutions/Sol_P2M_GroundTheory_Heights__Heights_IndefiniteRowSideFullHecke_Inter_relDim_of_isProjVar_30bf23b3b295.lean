-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_relDim_of_isProjVar_30bf23b3b295
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:04:49.005828+00:00
-- url     : https://prove2.me/submissions/724fff55-f71a-41d7-b96d-e58b234827be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivPrincipalDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CompsDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_of_ringKrullDim_eq_d98df862f27b


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
open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiHomogIdeal IsRelevant IsMultiProjPrime
  blockWeight)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {P : Ideal (MRing ι ℂ)} {e : ℕ} (h : IsProjVar P e) :
    GroundTheory.Heights₂.Heights.FieldNumbers.relDim P = (e : ℕ) := by
  rw [GroundTheory.Heights₂.Heights.FieldNumbers.relDim_of_ringKrullDim_eq P _ h.2]
  show ((((e + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ)) =
    (((e : ℕ) : ℤ) : WithBot (WithTop ℤ))
  congr 1
  push_cast
  ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
