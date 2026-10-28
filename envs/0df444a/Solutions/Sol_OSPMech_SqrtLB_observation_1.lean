-- Prove2me | solution 1 for OSPMech.SqrtLB.observation_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:32:14.402269+00:00
-- url     : https://prove2.me/submissions/75ee255a-6d52-4e05-bebb-5fab953eb779

import Mathlib
import Definitions.Def_OSPMech_SqrtLB_Model

open OSPMech.SqrtLB in
theorem solution {n : ℕ} {X : Type} (D : Fin n → Finset ℝ) (cost : Fin n → ℝ → X → ℝ)
    (t : ImplTree n X) (p : (Fin n → ℝ) → Fin n → ℝ) :
    IsOSP D cost t p ↔
      ∀ (pos : List ℕ) (i : Fin n) (a b : Fin n → ℝ), InDomain D a → InDomain D b →
        DivergeAt t pos i a b →
        p b i - p a i ≤ cost i (a i) (outcome t b) - cost i (a i) (outcome t a) := by
  unfold IsOSP
  constructor
  · intro h pos i a b ha hb hd
    have := h pos i a b ha hb hd
    linarith
  · intro h pos i a b ha hb hd
    have := h pos i a b ha hb hd
    linarith
