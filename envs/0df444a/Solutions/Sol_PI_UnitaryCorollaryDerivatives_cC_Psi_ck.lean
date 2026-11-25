-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cC_Psi_ck
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:41.727804+00:00
-- url     : https://prove2.me/submissions/0a43b488-7328-49c7-b5dd-344a2aec8d83

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CBLamnorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CCCNonneg
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cC_smul_ck
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dw


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
theorem _root_.solution {r : ℕ} {Q mm : ℕ} {φ : B.Mat k r → ℂ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    {f : B.Mat k r → E} (hf : B.CkOn (mm : ℕ∞) (B.GV k r) f) {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X)
    (hQ : Q + w.length ≤ mm) : B.CkOn (Q : ℕ∞) (B.GV k r) (B.Rw w (fun g => φ g • f g)) := by
  have h := cC_smul_ck hφ hf
  have hmono : B.CkOn ((Q + w.length : ℕ) : ℕ∞) (B.GV k r) (fun g => φ g • f g) := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hff⟩ := h g₀ hg₀
    exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast hQ), hff⟩
  have hR : B.Rw w (fun g => φ g • f g) = Dw (wL [] ++ wR w) (fun g => φ g • f g) := by
    rw [← dLR_eq]
    rfl
  rw [hR]
  apply CkOn_Dw
  · intro x hx
    simp only [wL, wR, List.map_nil, List.nil_append, List.mem_map] at hx
    obtain ⟨X, hX, rfl⟩ := hx
    exact hw X hX
  · simpa [wL, wR] using hmono
end PI.UnitaryCorollaryDerivatives
