-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_Dw_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:52.531816+00:00
-- url     : https://prove2.me/submissions/81380a7d-6dc8-4243-a010-7a81fe4ffce8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBB
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_dirL_apply


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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {K : ℝ} (hK : 0 ≤ K) (w : List (Bool × B.Mat k r))
    (hw : ∀ x ∈ w, ∀ g, ‖dirL x g‖ ≤ K * ‖g‖) :
    ∀ (Λ : B.Mat k r →L[ℝ] ℂ) (c : ℝ), 0 ≤ c → (∀ g, ‖Λ g‖ ≤ c * ‖g‖) → ∃ Λ' : B.Mat k r →L[ℝ] ℂ,
      Dw w (fun g => Λ g) = (fun g => Λ' g) ∧ ∀ g, ‖Λ' g‖ ≤ c * K ^ w.length * ‖g‖ := by
  have hD : ∀ (L : B.Mat k r →L[ℝ] ℂ) (x : Bool × B.Mat k r),
      Dx x (fun g => L g) = fun g => L (dirL x g) := by
    intro L x
    funext g
    rw [Dx_eq, dirL_apply]
    exact (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)).deriv
  induction w with
  | nil =>
    intro Λ c hc hΛ
    refine ⟨Λ, rfl, fun g => ?_⟩
    simpa using hΛ g
  | cons x w ih =>
    intro Λ c hc hΛ
    obtain ⟨Λ₁, h₁, hb₁⟩ := ih (fun y hy => hw y (by simp [hy])) Λ c hc hΛ
    refine ⟨Λ₁.comp (dirL x), ?_, fun g => ?_⟩
    · show Dx x (Dw w fun g => Λ g) = _
      rw [h₁, hD]
      rfl
    · have hx := hw x (by simp) g
      calc ‖(Λ₁.comp (dirL x)) g‖ = ‖Λ₁ (dirL x g)‖ := rfl
        _ ≤ c * K ^ w.length * ‖dirL x g‖ := hb₁ _
        _ ≤ c * K ^ w.length * (K * ‖g‖) :=
          mul_le_mul_of_nonneg_left hx (mul_nonneg hc (pow_nonneg hK _))
        _ = c * K ^ (x :: w).length * ‖g‖ := by
          rw [List.length_cons, pow_succ]
          ring
end PI.UnitaryCorollaryDerivatives
