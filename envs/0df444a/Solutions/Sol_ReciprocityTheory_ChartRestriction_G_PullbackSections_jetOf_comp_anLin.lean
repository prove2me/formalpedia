-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetOf_comp_anLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:21:19.110793+00:00
-- url     : https://prove2.me/submissions/750e2b20-3fa0-4f76-8bc2-6b0a33266a08

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anLin_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_tay_comp_anLin
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_mk_trunc_coe
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_subst
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psTrunc_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetMap_congr


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
open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {g g' : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (m : ℕ) {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0)
    (A : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) :
    jetOf m (θ ∘ A) = jetMap (anLin A) (anLin_mem A) (jetOf m θ) := by
  rw [jetOf, tay_comp_anLin hθ A, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psJet_subst m _ (anLin_cc A)]
  refine jetMap_congr _ _ _ _ (fun p => ?_) _
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.mk_trunc_coe]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
