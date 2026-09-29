-- Prove2me | solution 1 for W54.pow_smul_tateModule_eq_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/95611714-8bda-54bf-b462-b949f66d7ae6

import Definitions.Def_ModularCurve_EichlerShimuraData
import Mathlib.NumberTheory.Padics.RingHoms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_W54_pow_smul_tateModule_eq_vanishing

open ModularCurve

theorem solution {p : ℕ} {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    (n : ℕ) {x : ℕ → J} (hx : x ∈ TateModule p J) :
    (∃ y ∈ TateModule p J, (p ^ n : ℕ) • y = x) ↔ x n = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (p ^ n : ℕ) • y n = 0
    exact TateModule.pow_smul_apply hy n
  · intro hxn

    have key : ∀ k m, x m = p ^ k • x (m + k) := by
      intro k
      induction k with
      | zero => intro m; simp
      | succ k ih =>
        intro m
        calc x m = p ^ k • x (m + k) := ih m
          _ = p ^ k • (p • x (m + k + 1)) := by rw [hx.2 (m + k)]
          _ = (p ^ k * p) • x (m + k + 1) := by rw [mul_smul]
          _ = p ^ (k + 1) • x (m + (k + 1)) := by rw [← pow_succ, ← Nat.add_assoc]
    refine ⟨fun m => x (m + n), ⟨?_, fun m => ?_⟩, ?_⟩
    · simpa using hxn
    · have := hx.2 (m + n)
      simpa [Nat.add_right_comm m 1 n] using this
    · funext m
      exact (key n m).symm

end S_W54_pow_smul_tateModule_eq_vanishing
end P2MW
export P2MW.S_W54_pow_smul_tateModule_eq_vanishing (solution)
