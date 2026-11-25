-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.order_lg_sub_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:35:37.963118+00:00
-- url     : https://prove2.me/submissions/9c441f18-da11-4377-b6b6-2184230545c5

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_degree_eq_one

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
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution (G : LogFGL v d) (a : Fin d) : ((2 : ℕ) : ℕ∞) ≤ (G.lg a - X a).order := by
  classical
  apply MvPowerSeries.le_order
  intro e he
  have he' : e.degree < 2 := by exact_mod_cast he
  rw [map_sub]
  rcases (show e.degree = 0 ∨ e.degree = 1 by omega) with h0 | h1
  · have hz : e = 0 := by
      first
      | exact Finsupp.degree_eq_zero_iff.mp h0
      | exact (Finsupp.degree_eq_zero_iff e).mp h0
    rw [hz, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, G.lg_const,
      constantCoeff_X, sub_zero]
  · obtain ⟨b, rfl⟩ := degree_eq_one h1
    rw [G.lg_lin, coeff_X]
    by_cases hab : a = b
    · rw [hab, if_pos rfl, if_pos rfl, sub_self]
    · rw [if_neg hab, if_neg (fun h => hab ((Finsupp.single_left_injective one_ne_zero h).symm)),
        sub_zero]
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
