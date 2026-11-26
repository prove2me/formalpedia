-- Prove2me | solution 1 for PascalExtremes.q0_lt_pow_two_a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:00:45.461173+00:00
-- url     : https://prove2.me/submissions/7ea4bb6a-b5ec-45fb-8195-27c67382cc4d

module
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetB
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff


section
@[expose] public section
namespace PascalExtremes
private lemma pow_a_lt_pow_two_a {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    p ^ a < p ^ (2 * a) := by
  apply Nat.pow_lt_pow_right hp.one_lt
  omega
end PascalExtremes
end
end

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    q0 p a < p ^ (2 * a) := by
  have hpow : p ^ a < p ^ (2 * a) :=
    pow_a_lt_pow_two_a hp ha
  have hone : 1 < p ^ a := by
    calc
      1 < p := hp.one_lt
      _ ≤ p ^ a := by
        calc
          p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha
  simp only [q0]
  omega
end PascalExtremes
