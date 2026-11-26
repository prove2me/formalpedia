-- Prove2me | solution 1 for PascalExtremes.carryAt_iff_mod_pow_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:56:05.435125+00:00
-- url     : https://prove2.me/submissions/c1dd6c16-6f52-4536-aaef-d48ccdc6bd6e

module
public import Definitions.Def_PascalExtremes_Basic
public import Definitions.Def_PascalExtremes_Digits
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Kummer
public import Theorems.Thm_PascalExtremes_not_carryAt_iff_mod_pow_le
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff



set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution {p n k i : ℕ} (hp : 0 < p) (hkn : k ≤ n) :
    CarryAt p n k i ↔ n % p ^ i < k % p ^ i := by
  rw [← not_iff_not]
  simpa [not_lt] using
    (not_carryAt_iff_mod_pow_le (p := p) (n := n) (k := k) (i := i) hp hkn)
end PascalExtremes
