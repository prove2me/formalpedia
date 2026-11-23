-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__gB_prime_e07d09a6c9c7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:18.565728+00:00
-- url     : https://prove2.me/submissions/0d6f2a66-40d0-48ea-9ef3-b371734f2406

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Primes
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__lucas_list_6f32cc34af5b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.BasicNotions.Examples₂
private theorem zmod_pow_eq_one_of_pow_mod_eq_one {n a e : ℕ} (h : a ^ e % n = 1) : (a : ZMod n) ^ e = 1 := by
  rw [← Nat.cast_pow, ← ZMod.natCast_mod, h, Nat.cast_one]
private theorem zmod_pow_ne_one_of_pow_mod_ne_one {n a e : ℕ} (hn : 1 < n) (h : a ^ e % n ≠ 1) : (a : ZMod n) ^ e ≠ 1 := by
  intro hc
  apply h
  have h2 := (ZMod.natCast_eq_natCast_iff' (a ^ e) 1 n).1 (by push_cast; exact hc)
  rwa [Nat.mod_eq_of_lt hn] at h2
private theorem pow_mod_of_two_pow_window {a n e e' r s : ℕ} (k w : ℕ) (h : a ^ e % n = r) (he : 2 ^ k * e + w = e')
    (hs : r ^ (2 ^ k) * a ^ w % n = s) : a ^ e' % n = s := by
  subst he hs h
  rw [pow_add, pow_mul', Nat.mul_mod, Nat.pow_mod (a ^ e) (2 ^ k) n]
  conv_rhs => rw [Nat.mul_mod]
private theorem pow_17_mod_603339156001_eq_one : 17 ^ (603339156001 - 1) % 603339156001 = 1 := by
  have h : 17 ^ 140 % 603339156001 = 348356949902 := by decide
  have h := pow_mod_of_two_pow_window (e' := 35961) (s := 478198242302) 8 121 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 9206224) (s := 181240510064) 8 208 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 2356793578) (s := 346348232865) 8 234 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := (603339156001 - 1)) (s := 1) 8 32 h (by decide) (by decide)
  exact h
private theorem pow_17_div_2_mod_603339156001 : 17 ^ ((603339156001 - 1) / 2) % 603339156001 = 603339156000 := by
  have h : 17 ^ 70 % 603339156001 = 491406418909 := by decide
  have h := pow_mod_of_two_pow_window (e' := 17980) (s := 556796402038) 8 60 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 4603112) (s := 83557276685) 8 232 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 1178396789) (s := 237568077630) 8 117 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := ((603339156001 - 1) / 2)) (s := 603339156000) 8 16 h (by decide) (by decide)
  exact h
private theorem pow_17_div_3_mod_603339156001 : 17 ^ ((603339156001 - 1) / 3) % 603339156001 = 365611846549 := by
  have h : 17 ^ 46 % 603339156001 = 28777737558 := by decide
  have h := pow_mod_of_two_pow_window (e' := 11987) (s := 128651052966) 8 211 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 3068741) (s := 263160051639) 8 69 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 785597859) (s := 456159856265) 8 163 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := ((603339156001 - 1) / 3)) (s := 365611846549) 8 96 h (by decide) (by decide)
  exact h
private theorem pow_17_div_5_mod_603339156001 : 17 ^ ((603339156001 - 1) / 5) % 603339156001 = 553231665472 := by
  have h : 17 ^ 28 % 603339156001 = 351796961553 := by decide
  have h := pow_mod_of_two_pow_window (e' := 7192) (s := 177095013452) 8 24 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 1841244) (s := 539589860221) 8 92 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 471358715) (s := 445017026891) 8 251 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := ((603339156001 - 1) / 5)) (s := 553231665472) 8 160 h (by decide) (by decide)
  exact h
private theorem pow_17_div_7_mod_603339156001 : 17 ^ ((603339156001 - 1) / 7) % 603339156001 = 477321853338 := by
  have h : 17 ^ 20 % 603339156001 = 64044962676 := by decide
  have h := pow_mod_of_two_pow_window (e' := 5137) (s := 457003583668) 8 17 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 1315174) (s := 395624134141) 8 102 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 336684796) (s := 37680162908) 8 252 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := ((603339156001 - 1) / 7)) (s := 477321853338) 8 224 h (by decide) (by decide)
  exact h
private theorem pow_17_div_571_mod_603339156001 : 17 ^ ((603339156001 - 1) / 571) % 603339156001 = 490793655739 := by
  have h : 17 ^ 62 % 603339156001 = 455431005906 := by decide
  have h := pow_mod_of_two_pow_window (e' := 16122) (s := 153549637107) 8 250 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 4127484) (s := 12260657621) 8 252 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := ((603339156001 - 1) / 571)) (s := 490793655739) 8 96 h (by decide) (by decide)
  exact h
private theorem pow_17_div_599_mod_603339156001 : 17 ^ ((603339156001 - 1) / 599) % 603339156001 = 511931551140 := by
  have h : 17 ^ 60 % 603339156001 = 16189637017 := by decide
  have h := pow_mod_of_two_pow_window (e' := 15369) (s := 77263201842) 8 9 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 3934546) (s := 587303257437) 8 82 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := ((603339156001 - 1) / 599)) (s := 511931551140) 8 224 h (by decide) (by decide)
  exact h
end Formalism.BasicNotions.Examples₂
end

set_option autoImplicit false
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution : Nat.Prime 603339156001 := by
  refine lucas_list 603339156001 17 [2, 3, 5, 7, 571, 599] 8 (by norm_num) ?_ (zmod_pow_eq_one_of_pow_mod_eq_one pow_17_mod_603339156001_eq_one) ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> first  | norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_17_div_2_mod_603339156001]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_17_div_3_mod_603339156001]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_17_div_5_mod_603339156001]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_17_div_7_mod_603339156001]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_17_div_571_mod_603339156001]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_17_div_599_mod_603339156001]; decide)
end Formalism.BasicNotions.Examples₂
