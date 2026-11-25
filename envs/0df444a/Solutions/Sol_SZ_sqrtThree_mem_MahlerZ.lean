-- Prove2me | solution 1 for SZ.sqrtThree_mem_MahlerZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:50.175436+00:00
-- url     : https://prove2.me/submissions/3a18c9d7-a7c5-4eb0-9e10-b89750defb81

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
import Theorems.Thm_SZ_witXi_pos
import Theorems.Thm_SZ_even_floor_even_case
import Theorems.Thm_SZ_even_floor_odd_case
import Theorems.Thm_SZ_one_lt_sqrt_three

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution : Real.sqrt 3 ∈ MahlerZ := by
  refine ⟨one_lt_sqrt_three, witXi, ne_of_gt witXi_pos, fun n hn => ?_⟩
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨t, ht⟩ := he
    have ht1 : 1 ≤ t := by omega
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have : n = 2 * (s + 1) := by omega
    rw [this]
    exact even_floor_even_case s
  · obtain ⟨s, rfl⟩ := ho
    exact even_floor_odd_case s
end SZ
