-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptSumL_lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:42:40.374429+00:00
-- url     : https://prove2.me/submissions/613c0464-7070-40e6-9cd9-a269af263ef3

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptAdd_lg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptSumL_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution (G : LogFGL v d) {τ : Type*} :
    ∀ l : List (Fin d → MvPowerSeries τ C), (∀ x ∈ l, ∀ a, constantCoeff (x a) = 0) →
      ∀ b, subst (ptSumL G l) (G.lg b) = (l.map fun x => subst x (G.lg b)).sum
  | [], _, b => by
    simp only [ptSumL, List.map_nil, List.sum_nil]
    exact subst_zero_of_constantCoeff_zero (G.lg_const b)
  | x :: l, h, b => by
    have hl : ∀ x' ∈ l, ∀ a, constantCoeff (x' a) = 0 := fun x' hx' => h x' (by simp [hx'])
    rw [ptSumL, ptAdd_lg G (h x (by simp)) (ptSumL_const G l hl), solution G l hl b]
    simp
end ReciprocityTheory.ChartRestriction.G.Sh
