-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetOf_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:53:58.319457+00:00
-- url     : https://prove2.me/submissions/ef12f0f9-bcaa-4a6d-bda6-0f3318e2433a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetMap_congr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_mk_trunc_coe
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_subst
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psTrunc_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_partA


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
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (m : ℕ) (c : Fin g → ℂ) {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) :
    jetOf m (fun z => θ fun i => c i * z i) = jetScaleP m c (jetOf m θ) := by
  have ha : ∀ p : Fin 1 × Fin g, MvPowerSeries.constantCoeff
      (MvPowerSeries.C (c p.2) * MvPowerSeries.X p : MvPowerSeries (Fin 1 × Fin g) ℂ) = 0 := by
    intro p
    simp
  unfold jetOf jetScaleP
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.partA θ hθ c, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psJet_subst m _ ha]
  refine jetMap_congr _ _ _ _ (fun p => ?_) _
  have hco : (MvPowerSeries.C (c p.2) * MvPowerSeries.X p : MvPowerSeries (Fin 1 × Fin g) ℂ) =
      ((MvPolynomial.C (c p.2) * MvPolynomial.X p : MvPolynomial (Fin 1 × Fin g) ℂ) :
        MvPowerSeries (Fin 1 × Fin g) ℂ) := by
    simp
  rw [hco, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.mk_trunc_coe]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
