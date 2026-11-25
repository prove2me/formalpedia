-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_eq_graphPt_of_mem_4583e741b80e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:18:15.646123+00:00
-- url     : https://prove2.me/submissions/c131aa24-a0cf-42af-94fa-b6f068c23a78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpenPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenPoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_graphPt_natAdd_be63f7604ada
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsolatedFibreOpenPoly_natAdd_of_mem_4bb9909352d8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Topology Filter Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
theorem _root_.solution {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) :
    z = graphPt p (firstPart z) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun i => ?_) k
  · simp [graphPt, firstPart, Fin.append_left]
  · rw [natAdd_of_mem hz i, graphPt_natAdd]
end GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly
