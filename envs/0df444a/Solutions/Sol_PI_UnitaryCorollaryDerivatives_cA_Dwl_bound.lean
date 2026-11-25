-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cA_Dwl_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:14:21.145286+00:00
-- url     : https://prove2.me/submissions/6904f73a-3004-4024-8b55-8ce66972ae21

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dx_smooth
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dwl_lin
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cA_Dwl_append

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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution (lam : Bool × B.Mat k r → ℂ) {Λ : ℝ} (hΛ : 0 ≤ Λ) (g : B.Mat k r) (M : ℝ) :
    ∀ (w : List (Bool × B.Mat k r)) (F : B.Mat k r → E), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
      (∀ x ∈ w, ‖lam x‖ ≤ Λ) → (∀ s : List (Bool × B.Mat k r), s.Sublist w → ‖Dw s F g‖ ≤ M) →
      ‖Dwl lam w F g‖ ≤ (1 + Λ) ^ w.length * M := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro F _ _ hM
    simpa [Dwl, Dw] using hM [] (List.Sublist.refl _)
  | append_singleton w x ih =>
    intro F hF hl hM
    have hl' : ∀ y ∈ w, ‖lam y‖ ≤ Λ := fun y hy => hl y (by simp [hy])
    have hx : ‖lam x‖ ≤ Λ := hl x (by simp)
    rw [cA_Dwl_append, cA_Dwl_lin lam w (cA_Dx_smooth x hF) hF]
    have b1 := ih (Dx x F) (cA_Dx_smooth x hF) hl' (by
      intro s hs
      have := hM (s ++ [x]) (hs.append (List.Sublist.refl _))
      rwa [Dw_append] at this)
    have b2 := ih F hF hl' (fun s hs => hM s (hs.trans (List.sublist_append_left _ _)))
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM [] (List.nil_sublist _))
    calc ‖Dwl lam w (Dx x F) g + lam x • Dwl lam w F g‖
        ≤ (1 + Λ) ^ w.length * M + Λ * ((1 + Λ) ^ w.length * M) := by
          refine (norm_add_le _ _).trans (add_le_add b1 ?_)
          rw [norm_smul]
          exact mul_le_mul hx b2 (norm_nonneg _) hΛ
      _ = (1 + Λ) ^ (w ++ [x]).length * M := by simp [pow_succ]; ring
end PI.UnitaryCorollaryDerivatives
