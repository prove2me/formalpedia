-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetAug_jetOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:06:31.459155+00:00
-- url     : https://prove2.me/submissions/63ef1180-a39d-415b-80ae-14a333af190b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetAug_psJet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_constantCoeff_tay


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
theorem _root_.solution (m : ℕ) (θ : (Fin g → ℂ) → ℂ) : (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) (jetOf m θ) = θ 0 := by
  rw [jetOf, jetAug_psJet, constantCoeff_tay]
  show lD θ 0 (Multiset.toList 0) = θ 0
  rw [Multiset.toList_zero]
  exact iteratedFDeriv_zero_apply _
end ReciprocityTheory.ChartRestriction.G.PullbackSections
