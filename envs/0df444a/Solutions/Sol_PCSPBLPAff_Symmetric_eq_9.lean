-- Prove2me | solution 1 for PCSPBLPAff.Symmetric.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:32:03.539313+00:00
-- url     : https://prove2.me/submissions/e89c5e7a-a6a5-4c37-9e73-46686f9e2f5e

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

open PCSPBLPAff.Symmetric in
theorem solution {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (X : Instance τ ar) (𝔸 : RelStruct τ ar A) (w : Fin X.n → A → ℚ)
    (p : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ) (r : Fin X.n → A → ℤ)
    (q : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℤ)
    (hLP : IsLPSol X 𝔸 w p) (hAff : IsAffSol X 𝔸 r q) (u ℓ v : ℕ) :
    ∀ (j : Fin X.m) (k : Fin (ar (X.sym j))) (a : A),
      ((u : ℚ) * ℓ * w (X.scope j k) a + v * r (X.scope j k) a) =
        ∑ y ∈ Finset.univ.filter (fun y : Fin (ar (X.sym j)) → A => y k = a),
          ((u : ℚ) * ℓ * p j y + v * q j y) := by
  intro j k a
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hLP.2.2.2.2.2 j k a,
    ← hAff.2.2.2 j k a]
  rw [Int.cast_sum]
