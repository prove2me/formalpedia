-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.pb_Dw_mulL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:57.454824+00:00
-- url     : https://prove2.me/submissions/28e0c933-b08a-4aba-b470-c29ca824a91d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dw
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_congr
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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {w : List (Bool × B.Mat k r)} (hw : ∀ x ∈ w, B.inLie k r x.2) {f : B.Mat k r → ℂ}
    (hf : B.CkOn w.length (B.GV k r) f) :
    ∀ g ∈ B.GV k r, Dw w (fun g => ContinuousLinearMap.mul ℂ ℂ (f g)) g =
      ContinuousLinearMap.mul ℂ ℂ (Dw w f g) := by
  induction w with
  | nil => intro g _; rfl
  | cons x w ih =>
    have hw' : ∀ y ∈ w, B.inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hle : ((w.length : ℕ) : ℕ∞) ≤ ((x :: w).length : ℕ) := by exact_mod_cast Nat.le_succ _
    have e : (1 : ℕ∞) + (w.length : ℕ∞) = ((x :: w).length : ℕ) := by
      push_cast [List.length_cons]; ring
    intro g hg
    show Dx x (Dw w _) g = ContinuousLinearMap.mul ℂ ℂ (Dx x (Dw w f) g)
    rw [Dx_congr (hw x (by simp)) (ih hw' (sCkOn_mono hle hf)) g hg]
    have h1 := CkOn_diff (hw x (by simp)) (CkOn_Dw hw' (m := 1) (by rw [e]; exact hf)) hg hg
    have h2 := ((ContinuousLinearMap.mul ℂ ℂ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    rw [Dx_eq]
    exact h2.deriv
end PI.UnitaryCorollaryDerivatives
