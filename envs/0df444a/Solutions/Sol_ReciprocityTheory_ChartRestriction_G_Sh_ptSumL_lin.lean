-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptSumL_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:55:50.538898+00:00
-- url     : https://prove2.me/submissions/6dee7a9f-a8b0-4264-9883-ddd13281c50f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptAdd_lin
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
      ∀ a t, coeff (Finsupp.single t 1) (ptSumL G l a) =
        (l.map fun x => coeff (Finsupp.single t 1) (x a)).sum
  | [], _, a, t => by simp [ptSumL]
  | x :: l, h, a, t => by
    have hl : ∀ x' ∈ l, ∀ a, constantCoeff (x' a) = 0 := fun x' hx' => h x' (by simp [hx'])
    rw [ptSumL, ptAdd_lin G (h x (by simp)) (ptSumL_const G l hl), solution G l hl a t]
    simp
end ReciprocityTheory.ChartRestriction.G.Sh
