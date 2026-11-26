-- Prove2me | solution 1 for PascalExtremes.padicVal_choose_eq_carryCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:55:08.19604+00:00
-- url     : https://prove2.me/submissions/14040d5f-ca84-44e8-b44b-17ce50da1b3e

module
public import Definitions.Def_PascalExtremes_Basic
public import Definitions.Def_PascalExtremes_Digits
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Kummer
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff



set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution {p n k b : ℕ} [Fact p.Prime]
    (hkn : k ≤ n) (hnb : Nat.log p n < b) :
    padicValNat p (n.choose k) = carryCount p n k b := by
  simpa [carryCount, CarryAt] using
    (padicValNat_choose (p := p) (n := n) (k := k) (b := b) hkn hnb)
end PascalExtremes
