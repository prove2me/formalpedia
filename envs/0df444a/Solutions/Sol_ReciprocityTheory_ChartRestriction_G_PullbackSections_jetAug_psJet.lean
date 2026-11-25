-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetAug_psJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:31:47.844064+00:00
-- url     : https://prove2.me/submissions/98332838-9fe0-465e-b075-e898df3edd03

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetB
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psTrunc_eq


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
    (jetAug : Jet ℂ ι m →ₐ[ℂ] ℂ) (psJet m f) = MvPowerSeries.constantCoeff f := by
  rw [psJet, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq]
  show MvPolynomial.aeval (fun _ => (0 : ℂ)) _ = _
  rw [MvPolynomial.aeval_zero', Algebra.algebraMap_self, RingHom.id_apply, MvPolynomial.constantCoeff_eq,
    MvPowerSeries.coeff_truncTotal _ (by simp), MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
