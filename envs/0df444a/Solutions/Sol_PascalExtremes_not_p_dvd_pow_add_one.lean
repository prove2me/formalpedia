-- Prove2me | solution 1 for PascalExtremes.not_p_dvd_pow_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:00:37.059139+00:00
-- url     : https://prove2.me/submissions/befff530-228b-46f6-8c70-842075f6dc6b

module
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetB
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff



set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    ¬ p ∣ p ^ a + 1 := by
  have hpPow : p ∣ p ^ a := dvd_pow_self p (by omega)
  have hmod : (p ^ a + 1) % p = 1 := by
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hpPow, zero_add]
    simp [Nat.mod_eq_of_lt hp.one_lt]
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  exact one_ne_zero
end PascalExtremes
