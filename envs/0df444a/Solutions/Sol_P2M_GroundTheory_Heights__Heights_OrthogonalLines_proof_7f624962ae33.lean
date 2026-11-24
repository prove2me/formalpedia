-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrthogonalLines_proof_7f624962ae33
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:47.579659+00:00
-- url     : https://prove2.me/submissions/7f40dd47-2eb8-4686-abc1-70a74192f651

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
namespace GroundTheory.Heights₂.Heights
namespace OrthogonalLines
theorem _root_.solution (hQ : LinesQuotDegreeBound.Statement)
    (hL : LinesLineDegree.Statement) : OrthogonalLines.Statement := by
  intro K _ _ n a d ha hd _ μ hμ m k b c hbc hmk
  obtain ⟨τ, -, hτ⟩ := hQ K n a d ha hd m k b c hbc hmk
  have hf : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have key : ∀ j, (Module.finrank ℚ K : ℝ) * μ ≤
      Real.log (idealIndex (a (τ j))) - 1 / 2 * ∑ σ : K →+* ℂ, Real.log (d σ (τ j)) := by
    intro j
    have h := hμ (τ j)
    rw [hL K n a d (τ j), normalise, le_div_iff₀ hf] at h
    linarith
  have hsum : ∑ _j : Fin k, (Module.finrank ℚ K : ℝ) * μ ≤
      ∑ j, (Real.log (idealIndex (a (τ j))) - 1 / 2 * ∑ σ : K →+* ℂ, Real.log (d σ (τ j))) :=
    Finset.sum_le_sum fun j _ => key j
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [normalise, le_div_iff₀ hf]
  have e : (k : ℝ) * μ * (Module.finrank ℚ K : ℝ) = (k : ℝ) * ((Module.finrank ℚ K : ℝ) * μ) := by
    ring
  linarith
end OrthogonalLines
end GroundTheory.Heights₂.Heights
