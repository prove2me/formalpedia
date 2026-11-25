-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetTrunc_psJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:31:52.493002+00:00
-- url     : https://prove2.me/submissions/0112353a-f6ba-4bf4-ada4-9f6efae97034

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetB
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_psTrunc_succ_sub


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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι ℂ) :
    (jetTrunc : Jet ℂ ι (m + 1) →ₐ[ℂ] Jet ℂ ι m) (psJet (m + 1) f) = psJet m f := by
  rw [psJet, psJet]
  show Ideal.Quotient.mk _ (psTrunc (m + 1) f) = Ideal.Quotient.mk _ (psTrunc m f)
  rw [Ideal.Quotient.eq]
  exact Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.psTrunc_succ_sub f
end ReciprocityTheory.ChartRestriction.G.PullbackSections
