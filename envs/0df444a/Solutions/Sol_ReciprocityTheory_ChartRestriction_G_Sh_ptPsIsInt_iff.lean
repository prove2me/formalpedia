-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptPsIsInt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:28:15.131923+00:00
-- url     : https://prove2.me/submissions/7b1e1e6d-2013-42cd-911c-aab3a612c29d

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_symm


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
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution (f : PowerSeries C) : PsIsInt v f ↔ f ∈ ptIntSer v Unit := by
  unfold PsIsInt
  constructor
  · intro h α
    have hα : α = Finsupp.single () (α ()) := by
      ext
      exact Finsupp.single_eq_same.symm
    have h1 := h (α ())
    rw [hα]
    exact h1
  · intro h n
    exact h (Finsupp.single () n)
end ReciprocityTheory.ChartRestriction.G.Sh
