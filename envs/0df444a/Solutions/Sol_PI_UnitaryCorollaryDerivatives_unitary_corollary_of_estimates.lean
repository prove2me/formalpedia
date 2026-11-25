-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.unitary_corollary_of_estimates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:35:58.216142+00:00
-- url     : https://prove2.me/submissions/fa871137-9b87-484a-8e4a-7867568c7902

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_UnitaryCorollaryOfEstimates

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution (hC : CoreStar) (hD : DjWB) (hG : GfWB) (hM : WBmul) :
    Formalism.FourierDecayAlt.U.StarBoundOfCutoffOperator ∧ Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator := by
  constructor
  · intro k j ρ Wp Wq _ _ _ _ _ o κ Θ χ hΘ hχ Q mm₀ A₀ hQ
    obtain ⟨hcd, Cφ, hWB⟩ := hD k j ρ χ (Q + o) hχ
    obtain ⟨C, hCf⟩ := hC k j ρ Wp Wq o κ 0 Θ χ (fun g => χ (DjU k j ρ g)) hΘ hχ Q mm₀ A₀ hQ hcd
      (fun g hg => image_eq_zero_of_notMem_tsupport hg) ⟨Cφ, by simpa using hWB⟩
    refine ⟨C, fun f c hf => ?_⟩
    have := hCf f c hf
    simp only [Nat.cast_zero, zero_mul, sub_zero] at this
    exact this
  · intro k j ρ Wp Wq _ _ _ _ _ z z' o κ Θ χ χε ε hΘ hχ hε Q mm₀ A₀ hQ
    obtain ⟨hcd, C1, h1⟩ := hD k j ρ χ (Q + o) hχ
    obtain ⟨hcg, C2, h2⟩ := hG k (j + ρ) z z' χε ε (Q + o) hε
    obtain ⟨C3, h3⟩ := hM k (j + ρ) _ _ _ _ (Q + o) C1 C2 0 0 hcd hcg h1 h2
    rw [zero_add] at h3
    obtain ⟨C, hCf⟩ := hC k j ρ Wp Wq o κ (2 * (j + ρ + 1)) Θ χ
      (fun g => χ (DjU k j ρ g) * ((χε (Gf k (j + ρ) z z' g) : ℝ) : ℂ)) hΘ hχ Q mm₀ A₀ hQ (hcd.mul hcg)
      (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg]) ⟨C3, h3⟩
    refine ⟨C, fun f c hf => ?_⟩
    have := hCf f c hf
    convert this using 2
    · rfl
    · push_cast; ring
end PI.UnitaryCorollaryDerivatives
