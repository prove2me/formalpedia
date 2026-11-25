-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lift.VA.near_one_approximation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:16:50.098881+00:00
-- url     : https://prove2.me/submissions/3e4e74de-1000-402b-8a8d-ea836489f213

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_LiftSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_LargeSmall
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_RhoProjectionAssembly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lift_VA_disc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lift_VA_val_frac_of_one_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lift_VA_val_frac_of_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lift ReciprocityTheory.ChartRestriction.G.Lift.VA
open WithZero
namespace ReciprocityTheory.ChartRestriction.G.Lift.VA
theorem _root_.solution : NearOne := by
  intro Ω _ ι _ v hls i ε hε
  classical
  choose mj hmj1 hmj using fun j => disc 1 (ε j) (hε j)
  obtain ⟨y, hy1, hy2⟩ := hls i
  set m := (Finset.univ.sup mj) + 1 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hmj' : ∀ j, mj j ≤ m := fun j =>
    le_trans (Finset.le_sup (f := mj) (Finset.mem_univ j)) (Nat.le_succ _)
  refine ⟨y ^ m / (1 + y ^ m), val_frac_of_one_lt (v i) y hy1 m hm1, fun j hj => ?_⟩
  rw [val_frac_of_lt_one (v j) y (hy2 j hj) m hm1, ← mul_one (v j y ^ m)]
  exact hmj j m (hmj' j) _ _ (hy2 j hj) le_rfl
end ReciprocityTheory.ChartRestriction.G.Lift.VA
