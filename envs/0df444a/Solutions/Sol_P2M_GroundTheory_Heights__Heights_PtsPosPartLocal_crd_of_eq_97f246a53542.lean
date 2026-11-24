-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_crd_of_eq_97f246a53542
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:16.407585+00:00
-- url     : https://prove2.me/submissions/6874eca0-004a-4d16-8466-693389070ff4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_nrm_of_eq_9866b3b330bc

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.PtsPosPartLocal
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
variable {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
namespace GroundTheory.Heights₂.Heights.PtsPosPartLocal
theorem _root_.solution {w : ((k : K) → ι k) → ℂ} {y : Fin e → ℂ} (h : Ψ w = Fin.cons 1 y) : crd Ψ w = y := by
  funext i
  simp [crd, nrm_of_eq h, h]
end GroundTheory.Heights₂.Heights.PtsPosPartLocal
