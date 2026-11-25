-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.anLin_anPr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:50:40.993016+00:00
-- url     : https://prove2.me/submissions/7c6489b0-e9e7-4603-9d95-fad7e72aa787

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anPr_apply

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
theorem _root_.solution (i : Fin 2) (p : Fin 1 × Fin g) :
    anLin (anPr (g := g) i) p = MvPolynomial.X ((0 : Fin 1), anKap (i, p.2)) := by
  rw [anLin, Finset.sum_eq_single (anKap (i, p.2))]
  · rw [anPr_apply, Pi.single_eq_same, map_one, _root_.one_mul]
  · intro k _ hk
    simp [anPr_apply, Ne.symm hk]
  · simp
end ReciprocityTheory.ChartRestriction.G.PullbackSections
