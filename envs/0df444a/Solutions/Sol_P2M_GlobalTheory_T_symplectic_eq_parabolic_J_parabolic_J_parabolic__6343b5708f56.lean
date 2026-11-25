-- Prove2me | solution 1 for P2M_GlobalTheory_T_symplectic_eq_parabolic_J_parabolic_J_parabolic__6343b5708f56
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:16.151691+00:00
-- url     : https://prove2.me/submissions/55d79697-69a0-4ecb-bf72-8ba3211e5289

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticEqParabolicJParabolicJParabolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticEqParabolicJParabolicJParabolicStatement
import Theorems.Thm_GlobalTheory_SW_symplectic_eq_parabolic_J_parabolic_J_parabolic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∃ p₁ ∈ Matrix.symplecticGroup ι ℚ, ∃ p₂ ∈ Matrix.symplecticGroup ι ℚ, ∃ p₃ ∈ Matrix.symplecticGroup ι ℚ, p₁.toBlocks₂₁ = 0 ∧ p₂.toBlocks₂₁ = 0 ∧ p₃.toBlocks₂₁ = 0 ∧ σ = p₁ * Matrix.J ι ℚ * p₂ * Matrix.J ι ℚ * p₃ := by
  first | exact @GlobalTheory.SW.symplectic_eq_parabolic_J_parabolic_J_parabolic | exact GlobalTheory.SW.symplectic_eq_parabolic_J_parabolic_J_parabolic | (intros; apply GlobalTheory.SW.symplectic_eq_parabolic_J_parabolic_J_parabolic <;> assumption)
end _root_.GlobalTheory.T
