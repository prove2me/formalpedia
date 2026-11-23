-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__gA_prime_d730a2330e37
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:18.4869+00:00
-- url     : https://prove2.me/submissions/9cd2c228-ca5c-4460-980d-0caa6a5442a0

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
private theorem pow_34_mod_413718278401_eq_one : 34 ^ (413718278401 - 1) % 413718278401 = 1 := by
  have h : 34 ^ 96 % 413718278401 = 252715656822 := by decide
  have h := pow_mod_of_two_pow_window (e' := 24659) (s := 207305366940) 8 83 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 6312839) (s := 174963732253) 8 135 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 1616087025) (s := 382811176459) 8 241 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := (413718278401 - 1)) (s := 1) 8 0 h (by decide) (by decide)
  exact h
private theorem pow_34_div_2_mod_413718278401 : 34 ^ ((413718278401 - 1) / 2) % 413718278401 = 413718278400 := by
  have h : 34 ^ 48 % 413718278401 = 324403388117 := by decide
  have h := pow_mod_of_two_pow_window (e' := 12329) (s := 257352973644) 8 41 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 3156419) (s := 89195747387) 8 195 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 808043512) (s := 266060489695) 8 248 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := ((413718278401 - 1) / 2)) (s := 413718278400) 8 128 h (by decide) (by decide)
  exact h
private theorem pow_34_div_3_mod_413718278401 : 34 ^ ((413718278401 - 1) / 3) % 413718278401 = 89850750709 := by
  have h : 34 ^ 32 % 413718278401 = 207653270352 := by decide
  have h := pow_mod_of_two_pow_window (e' := 8219) (s := 151195948521) 8 27 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 2104279) (s := 4390086443) 8 215 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 538695675) (s := 365432487822) 8 251 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := ((413718278401 - 1) / 3)) (s := 89850750709) 8 0 h (by decide) (by decide)
  exact h
private theorem pow_34_div_5_mod_413718278401 : 34 ^ ((413718278401 - 1) / 5) % 413718278401 = 266539016536 := by
  have h : 34 ^ 19 % 413718278401 = 173908091450 := by decide
  have h := pow_mod_of_two_pow_window (e' := 4931) (s := 312299278426) 8 67 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 1262567) (s := 82833159278) 8 231 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 323217405) (s := 371405629095) 8 253 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := ((413718278401 - 1) / 5)) (s := 266539016536) 8 0 h (by decide) (by decide)
  exact h
private theorem pow_34_div_7_mod_413718278401 : 34 ^ ((413718278401 - 1) / 7) % 413718278401 = 309839479931 := by
  have h : 34 ^ 13 % 413718278401 = 255917949808 := by decide
  have h := pow_mod_of_two_pow_window (e' := 3522) (s := 309011577138) 8 194 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 901834) (s := 124660722223) 8 202 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 230869575) (s := 232318751438) 8 71 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := ((413718278401 - 1) / 7)) (s := 309839479931) 8 0 h (by decide) (by decide)
  exact h
private theorem pow_34_div_571_mod_413718278401 : 34 ^ ((413718278401 - 1) / 571) % 413718278401 = 319448285034 := by
  have h : 34 ^ 43 % 413718278401 = 411636473863 := by decide
  have h := pow_mod_of_two_pow_window (e' := 11055) (s := 223091634897) 8 47 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 2830275) (s := 103732990880) 8 195 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := ((413718278401 - 1) / 571)) (s := 319448285034) 8 0 h (by decide) (by decide)
  exact h
private theorem pow_34_div_599_mod_413718278401 : 34 ^ ((413718278401 - 1) / 599) % 413718278401 = 112346021238 := by
  have h : 34 ^ 41 % 413718278401 = 89470145152 := by decide
  have h := pow_mod_of_two_pow_window (e' := 10538) (s := 45675075330) 8 42 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := 2697975) (s := 310086335653) 8 247 h (by decide) (by decide)
  have h := pow_mod_of_two_pow_window (e' := ((413718278401 - 1) / 599)) (s := 112346021238) 8 0 h (by decide) (by decide)
  exact h
end Formalism.BasicNotions.Examples₂
end

set_option autoImplicit false
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution : Nat.Prime 413718278401 := by
  refine lucas_list 413718278401 34 [2, 3, 5, 7, 571, 599] 8 (by norm_num) ?_ (zmod_pow_eq_one_of_pow_mod_eq_one pow_34_mod_413718278401_eq_one) ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> first  | norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_34_div_2_mod_413718278401]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_34_div_3_mod_413718278401]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_34_div_5_mod_413718278401]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_34_div_7_mod_413718278401]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_34_div_571_mod_413718278401]; decide)
    · exact zmod_pow_ne_one_of_pow_mod_ne_one (by norm_num) (by rw [pow_34_div_599_mod_413718278401]; decide)
end Formalism.BasicNotions.Examples₂
