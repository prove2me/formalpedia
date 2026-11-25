-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_ptsIntegral_congr_mcPts_6069163e8079
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:32:04.90755+00:00
-- url     : https://prove2.me/submissions/b15857ff-0d26-44be-a07e-2748bbd869e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_sheetDensity_congr_mcPts_15faba685dcb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagRAux
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.DiagRAux
theorem _root_.solution (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hφ : ∀ j, ∀ z ∈ mcPts P, φ j z = φ' j z)
    (hg : ∀ z ∈ mcPts P, g z = g' z) : ptsIntegral P φ g = ptsIntegral P φ' g' := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · simp only [sheetDensity_congr_mcPts P _ hφ hg]
  · rfl
end GroundTheory.Heights₂.Heights.Inter.DiagRAux
