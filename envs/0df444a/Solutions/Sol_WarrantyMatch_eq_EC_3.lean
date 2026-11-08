-- Prove2me | solution 1 for WarrantyMatch.eq_EC_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:18:19.171574+00:00
-- url     : https://prove2.me/submissions/d0116edb-c07d-4319-8645-c9885c4dc902

import Mathlib
import Definitions.Def_WarrantyMatch_Model

open MeasureTheory

open WarrantyMatch in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℤ → Ω → ℤ) (ε : ℝ) (t : ℤ) (l : ℕ) (hdrift : KSDrift P D ε t) (z : ℕ) (k : ℤ) :
    |(P {ω | D t ω ≤ k}).toReal - (P {ω | D (t - l - z) ω ≤ k}).toReal| ≤
      ((l : ℝ) + z) * ε := by
  have key : ∀ n : ℕ, |(P {ω | D t ω ≤ k}).toReal - (P {ω | D (t - n) ω ≤ k}).toReal| ≤
      (n : ℝ) * ε := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hdrift (t - ((n + 1 : ℕ) : ℤ)) (by push_cast; linarith) k
      have e : t - ((n + 1 : ℕ) : ℤ) + 1 = t - (n : ℤ) := by push_cast; ring
      rw [e] at h
      calc |(P {ω | D t ω ≤ k}).toReal - (P {ω | D (t - ((n + 1 : ℕ) : ℤ)) ω ≤ k}).toReal|
          ≤ |(P {ω | D t ω ≤ k}).toReal - (P {ω | D (t - (n : ℤ)) ω ≤ k}).toReal|
            + |(P {ω | D (t - (n : ℤ)) ω ≤ k}).toReal
              - (P {ω | D (t - ((n + 1 : ℕ) : ℤ)) ω ≤ k}).toReal| := abs_sub_le _ _ _
        _ ≤ (n : ℝ) * ε + ε := add_le_add ih h
        _ = ((n + 1 : ℕ) : ℝ) * ε := by push_cast; ring
  have e : t - (l : ℤ) - (z : ℤ) = t - ((l + z : ℕ) : ℤ) := by push_cast; ring
  rw [e]
  have := key (l + z)
  push_cast at this
  exact this
