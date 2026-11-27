-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.anRen_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:37:58.673866+00:00
-- url     : https://prove2.me/submissions/ba119c83-defa-4ff4-9126-e25879edbd7b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anLin_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anJetMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anLin_anPr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_mk_trunc_coe
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
variable {Y : Scheme.{0}}
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (m : ℕ) (a : Jet ℂ (Fin 1 × Fin g) m) :
    anRen m (jetMap (anLin anSum) (anLin_mem _) a) =
      jetSubstP (S := ℂ) m (fun p : Fin 1 × Fin g => psTrunc m (addF ℂ g p.2)) a := by
  have hs : ∀ p : Fin 1 × Fin g, MvPolynomial.aeval (fun q : Fin 1 × Fin (2 * g) =>
      (MvPolynomial.X (anKap.symm q.2) : MvPolynomial (Fin 2 × Fin g) ℂ)) (anLin anSum p) =
      MvPolynomial.X ((0 : Fin 2), p.2) + MvPolynomial.X ((1 : Fin 2), p.2) := by
    intro p
    simp only [anSum, anLin_add, anLin_anPr, map_add, MvPolynomial.aeval_X, Equiv.symm_apply_apply]
  unfold anRen jetSubstP
  rw [anJetMap_comp _ _ _ _ _ (fun p => Ideal.add_mem _ (X_mem_orig _) (X_mem_orig _)) hs a]
  refine jetMap_congr _ _ _ _ (fun p => ?_) a
  have hc : MvPolynomial.constantCoeff (psTrunc m (addF ℂ g p.2)) = 0 := by
    rw [Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, MvPolynomial.constantCoeff_eq, MvPowerSeries.coeff_truncTotal _ (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [addF]
  have ha : (addF ℂ g p.2 : MvPowerSeries (Fin 2 × Fin g) ℂ) =
      ((MvPolynomial.X ((0 : Fin 2), p.2) + MvPolynomial.X ((1 : Fin 2), p.2) : MvPolynomial (Fin 2 × Fin g) ℂ) :
        MvPowerSeries (Fin 2 × Fin g) ℂ) := by simp [addF]
  simp only [hc, map_zero, sub_zero]
  rw [ha, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.mk_trunc_coe]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
