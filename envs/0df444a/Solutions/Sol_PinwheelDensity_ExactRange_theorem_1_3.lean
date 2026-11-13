-- Prove2me | solution 1 for PinwheelDensity.ExactRange.theorem_1_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T20:40:50.773112+00:00
-- url     : https://prove2.me/submissions/30716e8c-f1eb-41ad-9655-3ce9097f9850
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_coreP
import Theorems.Thm_PinwheelDensity_ExactRange_prop_2_3
import Definitions.Def_PinwheelDensity_ExactRange_checkRun
import Theorems.Thm_PinwheelDensity_ExactRange_theorem_E_1
import Theorems.Thm_PinwheelDensity_ExactRange_appendix_F_2_accepted_run

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.T12

open PinwheelDensity.ExactRange

/-- From the guarantee at `B = c m` and the sharpness family, `c m` is the greatest element of the
threshold set and equals `G m`. -/
theorem exact_of_guarantee (m : ℕ) (hm : 4 ≤ m) (hG : Guarantee m (c m)) :
    G m = ((c m : ℚ) : ℝ) ∧ IsGreatest (ThresholdSet m) ((c m : ℚ) : ℝ) := by
  have hmem : ((c m : ℚ) : ℝ) ∈ ThresholdSet m := by
    intro A hA hd
    exact hG A hA (by exact_mod_cast hd)
  have hub : ((c m : ℚ) : ℝ) ∈ upperBounds (ThresholdSet m) := by
    intro δ hδ
    by_contra hlt
    rw [not_le] at hlt
    -- choose x with 1/x ≤ δ - c m and x ≥ m
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (δ - ((c m : ℚ) : ℝ)))
    set x : ℕ := n + m with hx
    have hpos : 0 < δ - ((c m : ℚ) : ℝ) := sub_pos.mpr hlt
    have hxpos : (0 : ℝ) < x := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      rw [hx]; push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hxbig : 1 / (δ - ((c m : ℚ) : ℝ)) < x := by
      rw [hx]; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hinv : (1 : ℝ) / x ≤ δ - ((c m : ℚ) : ℝ) := by
      rw [div_le_iff₀ hxpos]
      rw [div_lt_iff₀ hpos] at hxbig
      linarith
    have h1 : 1 ≤ m := by omega
    obtain ⟨hns, hdens⟩ := (prop_2_3 m h1).1 x (by rw [hx]; omega)
    apply hns
    apply hδ
    · intro a ha
      simp only [sharpCore, List.cons_append, List.mem_cons, List.mem_append,
        List.mem_replicate, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | ⟨_, rfl⟩ | rfl
      · omega
      · omega
      · rw [hx]; omega
    · rw [hdens]
      push_cast
      linarith
  have hgr : IsGreatest (ThresholdSet m) ((c m : ℚ) : ℝ) := ⟨hmem, hub⟩
  exact ⟨hgr.csSup_eq, hgr⟩

theorem c_five : c 5 = 13 / 15 := by norm_num [c]

end PinwheelDensity.ExactRange.Dev.T12
end

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange

open PinwheelDensity.ExactRange.Dev.T12
theorem chk_theorem_1_3 :
    Guarantee 5 (13 / 15) ∧ G 5 = 13 / 15 ∧ IsGreatest (ThresholdSet 5) (13 / 15) := by
  obtain ⟨d, hd⟩ := appendix_F_2_accepted_run
  have hG : Guarantee 5 (13 / 15) := theorem_E_1 ⟨5, 13 / 15, 12⟩ d hd
  have hG' : Guarantee 5 (c 5) := by rw [c_five]; exact hG
  obtain ⟨h1, h2⟩ := exact_of_guarantee 5 (by norm_num) hG'
  rw [c_five] at h1 h2
  refine ⟨hG, ?_, ?_⟩
  · rw [h1]; norm_num
  · convert h2 using 1; norm_num

end PinwheelDensity.ExactRange
end

theorem solution : type_of% @PinwheelDensity.ExactRange.chk_theorem_1_3 := @PinwheelDensity.ExactRange.chk_theorem_1_3
