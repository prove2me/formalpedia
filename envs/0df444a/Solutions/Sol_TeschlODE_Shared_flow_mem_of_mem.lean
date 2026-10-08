-- Prove2me | solution 1 for TeschlODE.Shared.flow_mem_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:49:10.6295+00:00
-- url     : https://prove2.me/submissions/6d50c883-01b9-4489-81eb-91777f808b7d

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

open TeschlODE.Shared in
theorem solution {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (M : Set (Fin n → ℝ))
    (hM : IsOpen M) (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (hΦ : IsMaximalFlow f M I Φ) (x : Fin n → ℝ) (hx : x ∈ M) (t : ℝ) (ht : t ∈ I x) :
    Φ t x ∈ M := by
  exact (hΦ x hx).1.2.2.1 t ht
