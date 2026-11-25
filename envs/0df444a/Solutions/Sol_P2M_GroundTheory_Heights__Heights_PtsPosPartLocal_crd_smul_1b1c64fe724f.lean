-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_crd_smul_1b1c64fe724f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:15.635836+00:00
-- url     : https://prove2.me/submissions/a4be6e03-b718-4901-8902-c2fabc06535f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_nrm_smul_70d405fd40ea

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
theorem _root_.solution {t : ℂ} (ht : t ≠ 0) (w : ((k : K) → ι k) → ℂ) : crd Ψ (t • w) = crd Ψ w := by
  unfold crd
  rw [nrm_smul ht]
end GroundTheory.Heights₂.Heights.PtsPosPartLocal
