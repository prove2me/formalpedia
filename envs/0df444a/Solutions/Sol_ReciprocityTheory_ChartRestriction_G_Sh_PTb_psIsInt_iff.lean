-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.psIsInt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:29:19.231053+00:00
-- url     : https://prove2.me/submissions/54b8c70c-96fa-4735-a75b-a560ed81e90e

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_unit_finsupp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution {v : AddValuation C (WithTop ℝ)} {f : PowerSeries C} :
    PsIsInt v f ↔ MvIsInt v (σ := Unit) f := by
  constructor
  · intro h α
    rw [unit_finsupp α]
    exact h (α ())
  · intro h n
    exact h (Finsupp.single () n)
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
