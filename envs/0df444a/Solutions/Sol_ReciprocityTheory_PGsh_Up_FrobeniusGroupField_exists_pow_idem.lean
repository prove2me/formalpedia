-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.exists_pow_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:00:05.4665+00:00
-- url     : https://prove2.me/submissions/ea03adbb-c4ad-4d05-a4ee-2cfdabfb98cc

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsAdicCompleteOfBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {p : ℕ} [hp : Fact p.Prime]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution {S : Type} [Monoid S] [Finite S] (x : S) :
    ∃ M : ℕ, 0 < M ∧ x ^ (2 * M) = x ^ M := by
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ n)
  wlog h : a < b generalizing a b
  · exact this b a hab.symm he.symm (lt_of_le_of_ne (not_lt.1 h) hab.symm)
  set d := b - a with hd
  have hd0 : 0 < d := by omega
  have hstep : ∀ n, a ≤ n → x ^ (n + d) = x ^ n := by
    intro n hn
    have : n + d = (n - a) + b := by omega
    rw [this, pow_add, ← he, ← pow_add]; congr 1; omega
  have hk : ∀ k n, a ≤ n → x ^ (n + k * d) = x ^ n := by
    intro k
    induction k with
    | zero => intro n _; simp
    | succ k ih =>
      intro n hn
      rw [show n + (k + 1) * d = (n + k * d) + d by ring, hstep _ (by omega), ih n hn]
  refine ⟨d * (a + 1), Nat.mul_pos hd0 (Nat.succ_pos a), ?_⟩
  rw [show 2 * (d * (a + 1)) = d * (a + 1) + (a + 1) * d by ring]
  exact hk _ _ (by nlinarith)
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
