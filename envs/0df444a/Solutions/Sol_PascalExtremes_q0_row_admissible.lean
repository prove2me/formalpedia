-- Prove2me | solution 1 for PascalExtremes.q0_row_admissible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:43.084511+00:00
-- url     : https://prove2.me/submissions/e01e104d-e0e0-420c-8174-62b69a58944b

module
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetB
public import Theorems.Thm_PascalExtremes_mul_q0_eq_pow_three_add_one
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
theorem _root_.solution
    {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    AdmissibleRow (p ^ a + 1) (p ^ (3 * a) + 1) := by
  have hid := mul_q0_eq_pow_three_add_one hp (by omega : 1 ≤ a)
  refine ⟨?_, ?_⟩
  · have hq2 : 2 ≤ q0 p a := by
      have hpow := pow_a_lt_pow_two_a hp (by omega : 1 ≤ a)
      simp only [q0]
      omega
    rw [← hid]
    have hmpos : 0 < p ^ a + 1 := by positivity
    nlinarith
  · rw [← hid]
    exact dvd_mul_right _ _
end PascalExtremes
