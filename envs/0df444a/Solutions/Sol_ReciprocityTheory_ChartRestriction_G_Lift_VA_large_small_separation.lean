-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Lift.VA.large_small_separation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:16:45.639872+00:00
-- url     : https://prove2.me/submissions/0d716b60-1633-459a-9247-d7154f21c046

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
theorem _root_.solution : LargeSmall := by
  intro Ω _ ι _ v hbig hpair i
  classical
  have key : ∀ S : Finset ι, i ∉ S → ∃ y, 1 < v i y ∧ ∀ j ∈ S, v j y < 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      obtain ⟨x, hx⟩ := hbig i
      exact ⟨x, hx, by simp⟩
    | insert k S hk IH =>
      intro hiS
      have hki : k ≠ i := fun h => hiS (h ▸ Finset.mem_insert_self k S)
      have hiS' : i ∉ S := fun h => hiS (Finset.mem_insert_of_mem h)
      obtain ⟨y, hy1, hyS⟩ := IH hiS'
      obtain ⟨w, hw1, hw2⟩ := hpair i k (Ne.symm hki)
      obtain ⟨m, hm1, hm⟩ := disc (Finset.univ.sup fun j => v j w) 1 one_ne_zero
      have hwM : ∀ j, v j w ≤ Finset.univ.sup fun j => v j w :=
        fun j => Finset.le_sup (f := fun j => v j w) (Finset.mem_univ j)
      by_cases hky : v k y ≤ 1
      · refine ⟨y ^ m * w, ?_, ?_⟩
        · rw [map_mul, map_pow]
          exact lt_of_lt_of_le hw1 (le_mul_of_one_le_left' (one_le_pow_of_one_le' hy1.le m))
        · intro j hj
          rw [map_mul, map_pow]
          rcases Finset.mem_insert.mp hj with rfl | hjS
          · exact lt_of_le_of_lt (mul_le_of_le_one_left' (pow_le_one' hky m)) hw2
          · exact hm m le_rfl _ _ (hyS j hjS) (hwM j)
      · have hky' : 1 < v k y := lt_of_not_ge hky
        refine ⟨y ^ m / (1 + y ^ m) * w, ?_, ?_⟩
        · rw [map_mul, val_frac_of_one_lt (v i) y hy1 m hm1, one_mul]
          exact hw1
        · intro j hj
          rw [map_mul]
          rcases Finset.mem_insert.mp hj with rfl | hjS
          · rw [val_frac_of_one_lt (v j) y hky' m hm1, one_mul]
            exact hw2
          · rw [val_frac_of_lt_one (v j) y (hyS j hjS) m hm1]
            exact hm m le_rfl _ _ (hyS j hjS) (hwM j)
  obtain ⟨y, hy1, hy2⟩ := key (Finset.univ.erase i) (Finset.notMem_erase i _)
  exact ⟨y, hy1, fun j hj => hy2 j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)⟩
end ReciprocityTheory.ChartRestriction.G.Lift.VA
