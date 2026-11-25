-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.CCA.leibC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:57:21.927815+00:00
-- url     : https://prove2.me/submissions/4edca52b-e376-426e-b3e4-4f684d23eabb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompCA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CCA_sm_diff
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CCA_sm_Dx
import Theorems.Thm_P2M_PI_UnitaryCorollaryDerivatives_CCA_Dw_add__1dc732627764
import Theorems.Thm_P2M_PI_UnitaryCorollaryDerivatives_CCA_Dx_mul__aaf2ef076f89
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CCA_Dw_snoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.CCA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives.CCA
theorem _root_.solution (g : Mat k r) (w : List (Bool × Mat k r)) :
    ∀ (a b : Mat k r → ℂ), ContDiff ℝ ∞ a → ContDiff ℝ ∞ b → ∀ M : ℝ,
      (∀ w₁ w₂ : List (Bool × Mat k r), w₁.Sublist w → w₂.Sublist w → (w₁ ++ w₂).Perm w →
        ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) →
      ‖Dw w (fun g => a g * b g) g‖ ≤ 2 ^ w.length * M := by
  induction w using List.reverseRecOn with
  | nil =>
    intro a b ha hb M hM
    simpa [Dw, norm_mul] using hM [] [] (by simp) (by simp) (by simp)
  | append_singleton w x ih =>
    intro a b ha hb M hM
    rw [Dw_snoc, Dx_mul' x (sm_diff ha) (sm_diff hb),
      Dw_add' w ((sm_Dx x ha).mul hb) (ha.mul (sm_Dx x hb))]
    have h1 := ih (Dx x a) b (sm_Dx x ha) hb M (fun w₁ w₂ s1 s2 p => by
      have e : w₁ ++ [x] ++ w₂ = w₁ ++ x :: w₂ := by simp
      have hp : (w₁ ++ [x] ++ w₂).Perm (w ++ [x]) := by
        rw [e]
        exact List.perm_middle.trans ((p.cons x).trans (List.perm_append_singleton x w).symm)
      have := hM (w₁ ++ [x]) w₂ (s1.append (List.Sublist.refl _))
        (s2.trans (List.sublist_append_left _ _)) hp
      rwa [Dw_snoc] at this)
    have h2 := ih a (Dx x b) ha (sm_Dx x hb) M (fun w₁ w₂ s1 s2 p => by
      have hp : (w₁ ++ (w₂ ++ [x])).Perm (w ++ [x]) := by
        rw [← List.append_assoc]
        exact p.append_right [x]
      have := hM w₁ (w₂ ++ [x]) (s1.trans (List.sublist_append_left _ _))
        (s2.append (List.Sublist.refl _)) hp
      rwa [Dw_snoc] at this)
    calc _ ≤ ‖Dw w (fun g => Dx x a g * b g) g‖ + ‖Dw w (fun g => a g * Dx x b g) g‖ := norm_add_le _ _
      _ ≤ 2 ^ w.length * M + 2 ^ w.length * M := add_le_add h1 h2
      _ = 2 ^ (w ++ [x]).length * M := by
        rw [List.length_append, List.length_singleton, pow_succ]
        ring
end PI.UnitaryCorollaryDerivatives.CCA
