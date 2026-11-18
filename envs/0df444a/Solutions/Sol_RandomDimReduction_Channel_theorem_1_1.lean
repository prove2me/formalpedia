-- Prove2me | solution 1 for RandomDimReduction.Channel.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T18:02:49.541761+00:00
-- url     : https://prove2.me/submissions/ef3dfada-bc84-4308-8df7-25af863cdf0d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RandomDimReduction_Channel_RTP_isQuantumChannel
import Theorems.Thm_RandomDimReduction_Channel_RTP_embedded_twirl
import Theorems.Thm_RandomDimReduction_Channel_RTP_efficient

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory RandomDimReduction.Channel
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution :
    ∃ (c : ℝ) (K : ℕ), 0 < c ∧
      ∀ n k d : ℕ, 0 < n → 1 ≤ k → k ≤ d →
      (∃ L : Op (Word n d) →ₗ[ℂ] Op (Word n k),
        (∀ X, L X = RTP n k d X) ∧ WildeQIT.EntBreaking.IsQuantumChannel L) ∧
      (∀ (W : Matrix (Fin d) (Fin k) ℂ), Wᴴ * W = 1 → ∀ X₀ : Op (Word n k),
        RTP n k d (tensor n W * X₀ * (tensor n W)ᴴ) = twirl n k X₀) ∧
      (∀ eps : ℝ, 0 < eps → eps < 1 →
        ∃ C : Circuit (inputQubits n d) (inputQubits n k),
          (circuitSize C : ℝ) ≤ polyBound c K n d eps ∧
          diamond (fun X : Op (Word n d) =>
            circuitChannel C (encode n d X) - encode n k (RTP n k d X)) ≤
              ENNReal.ofReal eps) := by
  obtain ⟨c, K, hc, hC⟩ := RandomDimReduction.Channel.RTP_efficient
  refine ⟨c, K, hc, ?_⟩
  intro n k d hn hk hkd
  exact ⟨RandomDimReduction.Channel.RTP_isQuantumChannel n k d hn hk hkd,
    RandomDimReduction.Channel.RTP_embedded_twirl n k d hn hk hkd,
    hC n k d hn hk hkd⟩
