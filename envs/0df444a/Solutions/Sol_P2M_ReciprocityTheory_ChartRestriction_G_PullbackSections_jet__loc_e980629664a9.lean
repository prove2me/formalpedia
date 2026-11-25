-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_jet__loc_e980629664a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:49:37.412325+00:00
-- url     : https://prove2.me/submissions/c389ba41-0db0-4bc0-9110-427ca84ea0b5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_ne_zero_of_isUnit_jetOf
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_ValAt_valAt__ne_zero_iff_2a770214a5a4


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
theorem _root_.solution (m : ℕ) (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)) (hf : IsUnit (jetψ e hol m U hU f)) :
    e 0 cpt ∈ Y.basicOpen f := by
  rw [jetψ_apply] at hf
  exact (valAt'_ne_zero_iff (e 0) U (top_le_of_mem hU) f cpt).mp (ne_zero_of_isUnit_jetOf m hf)
end ReciprocityTheory.ChartRestriction.G.PullbackSections
