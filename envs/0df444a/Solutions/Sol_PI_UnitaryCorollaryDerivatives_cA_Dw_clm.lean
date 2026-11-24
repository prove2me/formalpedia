-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cA_Dw_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:33:49.990296+00:00
-- url     : https://prove2.me/submissions/8a79d0ca-3413-429d-ab6b-9588c1f299c7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dw
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_congr_loc
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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℂ] E')
    {U : Set (B.Mat k r)} (hU : IsOpen U) (w : List (Bool × B.Mat k r)) (hw : ∀ x ∈ w, B.inLie k r x.2)
    {f : B.Mat k r → E} (hf : B.CkOn (w.length : ℕ∞) U f) :
    ∀ g ∈ B.GV k r, g ∈ U → Dw w (fun h => L (f h)) g = L (Dw w f g) := by
  induction w with
  | nil => intro g _ _; rfl
  | cons x w ih =>
    intro g hg hgU
    have hw' : ∀ y ∈ w, B.inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hx : B.inLie k r x.2 := hw x (by simp)
    have hle : ((w.length : ℕ) : ℕ∞) ≤ ((x :: w).length : ℕ) := by exact_mod_cast Nat.le_succ _
    show Dx x (Dw w (fun h => L (f h))) g = L (Dx x (Dw w f) g)
    rw [Dx_congr_loc hx hU (f₂ := fun h => L (Dw w f h)) (ih hw' (sCkOn_mono hle hf)) g hg hgU]
    have hc : B.CkOn 1 U (Dw w f) := by
      apply CkOn_Dw hw'
      have : (1 : ℕ∞) + (w.length : ℕ∞) = ((x :: w).length : ℕ) := by simp; ring
      rw [this]; exact hf
    have h1 := CkOn_diff hx hc hgU hg
    have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    rw [Dx_eq]
    exact h2.deriv
end PI.UnitaryCorollaryDerivatives
