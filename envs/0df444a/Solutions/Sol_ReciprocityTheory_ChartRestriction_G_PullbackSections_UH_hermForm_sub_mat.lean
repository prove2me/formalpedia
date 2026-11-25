-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.hermForm_sub_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:27:36.794825+00:00
-- url     : https://prove2.me/submissions/24b76947-f609-4b07-87c6-1a83ba3c6ebb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_UnitHmA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.UH
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.UH
theorem _root_.solution (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm (H₁ - H₂) z w = hermForm H₁ z w - hermForm H₂ z w := by
  simp [hermForm, Matrix.sub_mulVec, dotProduct_sub]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.UH
