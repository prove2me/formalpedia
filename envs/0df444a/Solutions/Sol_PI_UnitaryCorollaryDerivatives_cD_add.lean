-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cD_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:46:45.434853+00:00
-- url     : https://prove2.me/submissions/bba2a4b2-2610-43a0-bb94-f738a17165d6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CCCNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStarOf
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dw_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono


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
theorem _root_.solution {Q : ℕ} {A₁ : ℝ} {O : Set (B.Mat k (j + ρ))} {F₁ F₂ : B.Mat k (j + ρ) → E} {C₁ C₂ c : ℝ}
    (h₁ : Good k j ρ Q A₁ O F₁ C₁ c) (h₂ : Good k j ρ Q A₁ O F₂ C₂ c) :
    Good k j ρ Q A₁ O (fun g => F₁ g + F₂ g) (C₁ + C₂) c := by
  obtain ⟨hc1, hz1, hb1⟩ := h₁
  obtain ⟨hc2, hz2, hb2⟩ := h₂
  refine ⟨CkOn_add hc1 hc2, fun g hg hO => by simp only [hz1 g hg hO, hz2 g hg hO, add_zero], ?_⟩
  intro u v hu hv hl g hg
  have hw : ∀ x ∈ wL u ++ wR v, B.inLie k (j + ρ) x.2 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx
      exact (hu X hX).1.1
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx
      exact (hv X hX).1.1
  have hlen : (((wL u ++ wR v).length : ℕ) : ℕ∞) ≤ (Q : ℕ∞) := by
    simp only [wL, wR, List.length_append, List.length_map]
    exact_mod_cast hl
  have hadd := Dw_add hw (sCkOn_mono hlen hc1) (sCkOn_mono hlen hc2) g hg
  have e1 := hb1 u v hu hv hl g hg
  have e2 := hb2 u v hu hv hl g hg
  rw [dLR_eq] at e1 e2 ⊢
  rw [hadd]
  have hpos : 0 ≤ B.gN g ^ A₁ := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  calc B.gN g ^ A₁ * ‖Dw (wL u ++ wR v) F₁ g + Dw (wL u ++ wR v) F₂ g‖ ≤
        B.gN g ^ A₁ * (‖Dw (wL u ++ wR v) F₁ g‖ + ‖Dw (wL u ++ wR v) F₂ g‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hpos
    _ = B.gN g ^ A₁ * ‖Dw (wL u ++ wR v) F₁ g‖ + B.gN g ^ A₁ * ‖Dw (wL u ++ wR v) F₂ g‖ :=
        mul_add _ _ _
    _ ≤ C₁ * c + C₂ * c := add_le_add e1 e2
    _ = (C₁ + C₂) * c := by ring
end PI.UnitaryCorollaryDerivatives
