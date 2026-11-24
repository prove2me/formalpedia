-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:56.769809+00:00
-- url     : https://prove2.me/submissions/569d64af-83ef-4613-b14c-7eda681ef7f6

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qn14
theorem _root_.solution :
    ∀ {a : WithBot ℕ∞} {k : ℕ},
    a + (1 : WithBot ℕ∞) ≤ (↑(k + (1 : ℕ)) : WithBot ℕ∞) → a ≤ (↑k : WithBot ℕ∞) := by
  intro a k h
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by
        rw [← WithBot.coe_le_coe]
        exact h
      rw [top_add, top_le_iff] at h1
      exact ENat.coe_ne_top _ h1
    | coe n =>
      have h1 : ((n : ℕ∞) + 1 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by
        rw [← WithBot.coe_le_coe]
        exact h
      have h2 : n + 1 ≤ k + 1 := by exact_mod_cast h1
      have h3 : (n : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast (Nat.le_of_succ_le_succ h2)
      exact WithBot.coe_le_coe.mpr h3
end UpperTheory.Reformulated.B.Qn14
