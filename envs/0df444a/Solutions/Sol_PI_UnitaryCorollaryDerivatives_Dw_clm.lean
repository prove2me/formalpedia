-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.Dw_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:43.379471+00:00
-- url     : https://prove2.me/submissions/53ddc8b2-22f8-41d8-9264-4ebf61200051

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_WeightBoundMultiplicative
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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] (L : E →L[ℂ] E') (w : List (Bool × B.Mat k r)) (hw : ∀ x ∈ w, B.inLie k r x.2)
    {f : B.Mat k r → E} (hf : B.CkOn (w.length : ℕ∞) (B.GV k r) f) :
    ∀ g ∈ B.GV k r, Dw w (fun h => L (f h)) g = L (Dw w f g) := by
  induction w with
  | nil => intro g _; rfl
  | cons x w ih =>
    intro g hg
    have hw' : ∀ y ∈ w, B.inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hx : B.inLie k r x.2 := hw x (by simp)
    have hle : ((w.length : ℕ) : ℕ∞) ≤ ((x :: w).length : ℕ) := by exact_mod_cast Nat.le_succ _
    show Dx x (Dw w (fun h => L (f h))) g = L (Dx x (Dw w f) g)
    rw [Dx_congr hx (ih hw' (sCkOn_mono hle hf)) g hg]
    have hc : B.CkOn 1 (B.GV k r) (Dw w f) := by
      apply CkOn_Dw hw'
      have : (1 : ℕ∞) + (w.length : ℕ∞) = ((x :: w).length : ℕ) := by simp; ring
      rw [this]; exact hf
    have h1 := CkOn_diff hx hc hg hg
    have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    rw [Dx_eq]
    exact h2.deriv
end PI.UnitaryCorollaryDerivatives
