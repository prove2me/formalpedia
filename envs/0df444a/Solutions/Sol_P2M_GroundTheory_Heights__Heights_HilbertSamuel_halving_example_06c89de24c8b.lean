-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_halving_example_06c89de24c8b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:06.549144+00:00
-- url     : https://prove2.me/submissions/a9011ebc-036e-4c0e-8a1c-c9896425351f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt MeasureTheory Module Filter
  Topology Asymptotics Matrix
open scoped ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution :
    (∃ C : ℝ, ∀ n : ℕ, |1 / ((n : ℝ) + 1)| ≤ C) ∧
    Tendsto (fun n : ℕ ↦ 1 / (((2 * n : ℕ) : ℝ) + 1) - 1 / ((n : ℝ) + 1) / 2) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) + 1) - 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨⟨1, fun n ↦ ?_⟩, ?_, ?_⟩
  · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [abs_of_pos (by positivity), div_le_one hn]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · have h2 := h0.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
    simpa using h2.sub (h0.div_const 2)
  · have h1 := h0.comp (tendsto_add_atTop_nat 1)
    simpa using h1.sub h0
end GroundTheory.Heights₂.Heights.HilbertSamuel
