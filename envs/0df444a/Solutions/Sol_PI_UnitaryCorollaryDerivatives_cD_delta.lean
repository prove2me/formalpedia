-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cD_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:52.348499+00:00
-- url     : https://prove2.me/submissions/f656c992-b8d8-48ac-a2d4-e9d781b2a164

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CCCNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStarOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k j ρ : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {χ : ℂ → ℂ} (hχ : IsCutC χ) : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ tsupport χ, δ ≤ ‖z‖ := by
  obtain ⟨-, -, h0⟩ := hχ
  have ho : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho 0 h0
  refine ⟨ε, hε, fun z hz => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact hball (by simpa [Metric.mem_ball, dist_zero_right] using hlt) hz
end PI.UnitaryCorollaryDerivatives
