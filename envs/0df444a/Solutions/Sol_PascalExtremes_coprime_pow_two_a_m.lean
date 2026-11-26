-- Prove2me | solution 1 for PascalExtremes.coprime_pow_two_a_m
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:41.683799+00:00
-- url     : https://prove2.me/submissions/d6f5cba3-db9b-4153-b29c-0378be0f4538

module
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetB
public import Theorems.Thm_PascalExtremes_not_p_dvd_pow_add_one

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    Nat.Coprime (p ^ (2 * a)) (p ^ a + 1) := by
  rw [Nat.coprime_pow_left_iff (by omega)]
  exact (hp.coprime_iff_not_dvd).2 (not_p_dvd_pow_add_one hp ha)
end PascalExtremes
