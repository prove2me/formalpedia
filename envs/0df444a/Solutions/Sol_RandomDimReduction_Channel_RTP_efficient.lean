-- Prove2me | solution 1 for RandomDimReduction.Channel.RTP_efficient
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:37:51.8958+00:00
-- url     : https://prove2.me/submissions/f9293106-1d77-401e-94b6-38f561500567
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RandomDimReduction_Channel_algorithm52_efficient_of_schur
import Theorems.Thm_RandomDimReduction_Channel_theorem_5_1
import Theorems.Thm_RandomDimReduction_Channel_theorem_5_3

set_option autoImplicit false

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

open RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution :
    ∃ (c : ℝ) (K : ℕ), 0 < c ∧
      ∀ n k d : ℕ, 0 < n → 1 ≤ k → k ≤ d →
      ∀ eps : ℝ, 0 < eps → eps < 1 →
        ∃ C : Circuit (inputQubits n d) (inputQubits n k),
          (circuitSize C : ℝ) ≤ polyBound c K n d eps ∧
          diamond (fun X : Op (Word n d) =>
            circuitChannel C (encode n d X) - encode n k (RTP n k d X)) ≤
              ENNReal.ofReal eps := by
  obtain ⟨c₀, K₀, hc₀, κ, S, hS⟩ := theorem_5_1
  obtain ⟨c, K, hc, h⟩ := algorithm52_efficient_of_schur c₀ K₀ hc₀ κ S hS
  refine ⟨c, K, hc, ?_⟩
  intro n k d hn hk hkd eps heps heps1
  obtain ⟨C, hsize, herr⟩ := h n k d hn hk hkd eps heps heps1
  refine ⟨C, hsize, ?_⟩
  simpa only [(theorem_5_3 n k d hn hk hkd (κ n) (S n d) (S n k)).1] using herr
