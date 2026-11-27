-- Prove2me | solution 1 for PositivityTheory.ThKR.Sieg.map_mul_right_of_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:23:24.352052+00:00
-- url     : https://prove2.me/submissions/4e56e610-b1c0-4b1a-9845-55dc4524156a

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulNn
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_SiegelHaar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory MeasureTheory.Measure Topology Set
open scoped NNReal ENNReal Pointwise
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Sieg
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {r : ℕ}
namespace PositivityTheory.ThKR.Sieg
theorem _root_.solution (ν : Measure G) [ν.IsHaarMeasure] (b : G) (φ : G ≃ₜ* G) (hφ : ∀ p, φ p = b⁻¹ * p * b) :
    ν.map (· * b) = ((mulEquivHaarChar φ)⁻¹ : ℝ≥0) • ν := by
  have e : (fun p => p * b) = φ ∘ fun p => b * p * 1 * b * b⁻¹ := funext fun p => by simp [hφ]
  rw [e, ← Measure.map_map (g := φ) φ.continuous.measurable (by fun_prop)]
  simp only [mul_one, mul_inv_cancel_right, map_mul_left_eq_self]
  conv_rhs => rw [← mulEquivHaarChar_smul_map ν φ]
  rw [smul_smul, inv_mul_cancel₀ (mulEquivHaarChar_pos φ).ne', one_smul]
end PositivityTheory.ThKR.Sieg
