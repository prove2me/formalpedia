-- Prove2me | solution 1 for OddPerfectNumber.no_euler_ge_nine_ge_thirteen
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T23:26:10.80186+00:00
-- url     : https://prove2.me/submissions/8b5b58dd-e9c2-4ea7-a12b-e80814ce70bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_dris_parametrisation
import Theorems.Thm_OddPerfectNumber_no_dris_thirteen_s_eq_one
import Theorems.Thm_OddPerfectNumber_no_dris_thirteen_s_ge_two

open OddPerfectNumber

theorem solution (p k m : Nat) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m) :
    (∑ d ∈ (p ^ k).divisors, d) * (∑ d ∈ (m ^ 2).divisors, d) != 2 * (p ^ k * m ^ 2) := by
  -- Boolean goal: prove the `≠` version, then convert with `bne_iff_ne`.
  suffices hne : (∑ d ∈ (p ^ k).divisors, d) * (∑ d ∈ (m ^ 2).divisors, d) ≠ 2 * (p ^ k * m ^ 2) by
    exact bne_iff_ne.mpr hne
  intro heq
  have hp2 : p ≠ 2 := by
    intro h2
    subst h2
    norm_num at hp4
  -- Children were published with boolean `!=`; bridge `Ne` to `(bne) = true`.
  have hp2b : (p != 2) = true := bne_iff_ne.mpr hp2
  have hm0 : m ≠ 0 := by
    obtain ⟨t, ht⟩ := hm
    omega
  have hkodd : k % 2 = 1 := by omega
  rcases dris_parametrisation p k m hp hp2 hkodd hm0 heq with ⟨s, hs_pos, h_two, h_sigma⟩
  by_cases hs1 : s = 1
  · subst hs1
    exact no_dris_thirteen_s_eq_one p k m 1 hp hp2b hp4 hk4 hk13 hm hpm rfl ⟨h_two, h_sigma⟩
  · have hs2 : 2 ≤ s := by omega
    exact no_dris_thirteen_s_ge_two p k m s hp hp2b hp4 hk4 hk13 hm hpm hs2 ⟨h_two, h_sigma⟩
