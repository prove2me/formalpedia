-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.dw_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:15.636569+00:00
-- url     : https://prove2.me/submissions/7b50ee93-2189-40b3-af0d-cad5dcf3a236

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_EntryLeLsz
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sc_back
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dw_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCost
private lemma LdV_ofReal_smul {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℝ) (Y : B.Mat k r) (F : B.Mat k r → E) (g : B.Mat k r) :
    B.LdV (((c : ℝ) : ℂ) • Y) F g = ((c : ℝ) : ℂ) • B.LdV Y F g := by
  simp only [B.LdV]
  have e : ∀ t : ℝ, ((t : ℂ) • (((c : ℝ) : ℂ) • Y)) = (((c * t : ℝ)) : ℂ) • Y := by
    intro t; rw [smul_smul]; congr 1; push_cast; ring
  simp only [e]
  rw [deriv_comp_mul_left (𝕜 := ℝ) c (fun s : ℝ => F (NormedSpace.exp (-((s : ℂ) • Y)) * g)) 0,
    mul_zero, Complex.coe_smul]
private lemma RdV_ofReal_smul {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℝ) (Y : B.Mat k r) (F : B.Mat k r → E) (g : B.Mat k r) :
    Formalism.REAL.RdV (((c : ℝ) : ℂ) • Y) F g = ((c : ℝ) : ℂ) • Formalism.REAL.RdV Y F g := by
  simp only [Formalism.REAL.RdV]
  have e : ∀ t : ℝ, ((t : ℂ) • (((c : ℝ) : ℂ) • Y)) = (((c * t : ℝ)) : ℂ) • Y := by
    intro t; rw [smul_smul]; congr 1; push_cast; ring
  simp only [e]
  rw [deriv_comp_mul_left (𝕜 := ℝ) c (fun s : ℝ => F (g * NormedSpace.exp ((s : ℂ) • Y))) 0,
    mul_zero, Complex.coe_smul]
private lemma Dx_eq_lsz_smul_Dx_scx {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : Bool × B.Mat k r) (F : B.Mat k r → E) (g : B.Mat k r) :
    P.BetaSesquilinearity.Dx x F g = ((lsz x.2 : ℝ) : ℂ) • P.BetaSesquilinearity.Dx (scx x) F g := by
  obtain ⟨b, X⟩ := x
  have hX : X = ((lsz X : ℝ) : ℂ) • sc X := (sc_back X).symm
  cases b
  · show Formalism.REAL.RdV X F g = ((lsz X : ℝ) : ℂ) • Formalism.REAL.RdV (sc X) F g
    conv_lhs => rw [hX]
    exact RdV_ofReal_smul _ _ _ _
  · show B.LdV X F g = ((lsz X : ℝ) : ℂ) • B.LdV (sc X) F g
    conv_lhs => rw [hX]
    exact LdV_ofReal_smul _ _ _ _
end PI.UnitaryGroupMassFormula.UsCost
end
end

set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (w : List (Bool × B.Mat k r)) (f : B.Mat k r → E) :
    P.BetaSesquilinearity.Dw w f = fun g => (((w.map (fun x => lsz x.2)).prod : ℝ) : ℂ) • P.BetaSesquilinearity.Dw (w.map scx) f g := by
  induction w with
  | nil => funext g; simp [P.BetaSesquilinearity.Dw]
  | cons x w ih =>
    funext g
    have h1 : P.BetaSesquilinearity.Dw (x :: w) f = P.BetaSesquilinearity.Dx x (P.BetaSesquilinearity.Dw w f) := rfl
    have h2 : P.BetaSesquilinearity.Dw ((x :: w).map scx) f = P.BetaSesquilinearity.Dx (scx x) (P.BetaSesquilinearity.Dw (w.map scx) f) := rfl
    rw [h1, h2, Dx_eq_lsz_smul_Dx_scx, ih]
    have h3 : P.BetaSesquilinearity.Dx (scx x) (fun g => (((w.map (fun x => lsz x.2)).prod : ℝ) : ℂ) • P.BetaSesquilinearity.Dw (w.map scx) f g)
        = fun g => (((w.map (fun x => lsz x.2)).prod : ℝ) : ℂ) • P.BetaSesquilinearity.Dx (scx x) (P.BetaSesquilinearity.Dw (w.map scx) f) g :=
      P.BetaSesquilinearity.Dw_smul _ [scx x] _
    rw [h3, List.map_cons, List.prod_cons, Complex.ofReal_mul, mul_smul]
end PI.UnitaryGroupMassFormula.UsCost
