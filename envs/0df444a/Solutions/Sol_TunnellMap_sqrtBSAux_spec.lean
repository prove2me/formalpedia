-- Prove2me | solution 1 for TunnellMap.sqrtBSAux_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:40.641512+00:00
-- url     : https://prove2.me/submissions/10315dcb-87e4-4fa3-8f1a-eb5783c4f657

import Mathlib
import Definitions.Def_TunnellMap_KernelArith

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (n : ℕ) :
    ∀ fuel lo hi, lo < hi → hi ≤ lo + 1 + fuel → lo * lo ≤ n → n < hi * hi →
      (sqrtBSAux n fuel lo hi) * (sqrtBSAux n fuel lo hi) ≤ n ∧
        n < (sqrtBSAux n fuel lo hi + 1) * (sqrtBSAux n fuel lo hi + 1) := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi hlt hle hlo hhi
      have hhieq : hi = lo + 1 := by omega
      subst hhieq
      exact ⟨hlo, hhi⟩
  | succ fuel ih =>
      intro lo hi hlt hle hlo hhi
      rw [sqrtBSAux]
      by_cases hstop : hi ≤ lo + 1
      · rw [if_pos hstop]
        have hhieq : hi = lo + 1 := by omega
        subst hhieq
        exact ⟨hlo, hhi⟩
      · rw [if_neg hstop]
        simp only []
        set mid := (lo + hi) / 2 with hmid
        have hmid₁ : lo < mid := by omega
        have hmid₂ : mid < hi := by omega
        by_cases hm : mid * mid ≤ n
        · rw [if_pos hm]
          exact ih mid hi hmid₂ (by omega) hm hhi
        · rw [if_neg hm]
          exact ih lo mid hmid₁ (by omega) hlo (by omega)
end TunnellMap
