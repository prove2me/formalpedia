-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.ne_zero_of_isUnit_jetOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:23:33.426347+00:00
-- url     : https://prove2.me/submissions/0e486046-fec5-4e39-827b-65034c8ebf20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetAug_jetOf

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (m : ℕ) {θ : (Fin g → ℂ) → ℂ} (h : IsUnit (jetOf m θ)) : θ 0 ≠ 0 := by
  have := h.map (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ)
  rw [jetAug_jetOf] at this
  exact this.ne_zero
end ReciprocityTheory.ChartRestriction.G.PullbackSections
