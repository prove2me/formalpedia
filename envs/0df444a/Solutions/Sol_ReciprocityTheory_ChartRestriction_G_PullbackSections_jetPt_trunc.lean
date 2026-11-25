-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:04:45.89363+00:00
-- url     : https://prove2.me/submissions/f1829857-7ca7-40f7-9e8a-2f79e67ae3b7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetTrunc_jetOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_nbhdPt_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_spec_comp_nbhdPt


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
variable {g : ℕ} {Y : Scheme.{0}}
variable (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (m : ℕ) :
    spMap ((jetTrunc : Jet ℂ (Fin 1 × Fin g) (m + 1) →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) : _ →+* _) ≫
      jetPt e hol (m + 1) = jetPt e hol m := by
  unfold jetPt
  rw [spMap, spec_comp_nbhdPt]
  refine nbhdPt_congr _ _ fun U hU => ?_
  ext f
  rw [CommRingCat.comp_apply, jetψ_apply, jetψ_apply]
  exact jetTrunc_jetOf m _
end ReciprocityTheory.ChartRestriction.G.PullbackSections
