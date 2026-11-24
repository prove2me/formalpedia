-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Ydd3.withBot_eq_of_le_of_add_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:36.037869+00:00
-- url     : https://prove2.me/submissions/abf98ef6-9a69-4cb4-af86-5b3d829feeed

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WithBotEqOfLeOfAddOneLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Ydd3
theorem _root_.solution :
    ∀ {x : WithBot ℕ∞} {c : ℕ},
      (↑c : WithBot ℕ∞) ≤ x → x + (1 : WithBot ℕ∞) ≤ (↑(c + (1 : ℕ)) : WithBot ℕ∞) → x = (↑c : WithBot ℕ∞) := by
  intro x c h1 h2
  induction x using WithBot.recBotCoe with
  | bot => exact le_antisymm bot_le h1
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h3 : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((c + 1 : ℕ) : ℕ∞) := by exact_mod_cast h2
      rw [top_add, top_le_iff] at h3
      exact ENat.coe_ne_top _ h3
    | coe n =>
      have h3 : c ≤ n := by exact_mod_cast h1
      have h4 : n + 1 ≤ c + 1 := by exact_mod_cast h2
      have h5 : n = c := by omega
      subst h5
      rfl
end UpperTheory.Reformulated.B.Ydd3
