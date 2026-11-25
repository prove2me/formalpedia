-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.CRH.chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:37.728844+00:00
-- url     : https://prove2.me/submissions/02e158a7-f1b1-4e4d-9884-98ba8e98f9d3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_cd_iter
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_cd_ofReal
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_dif
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_hd_Dx


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
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.CRH
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives.CRH
theorem _root_.solution (x : Bool × Mat k r) {ψ : Mat k r → ℝ} {h : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hh : ContDiff ℝ ∞ h)
    (q : ℕ) :
    Dx x (fun g => ((iteratedDeriv q h (ψ g) : ℝ) : ℂ)) =
      fun g => ((iteratedDeriv (q + 1) h (ψ g) : ℝ) : ℂ) * Dx x (fun g => ((ψ g : ℝ) : ℂ)) g := by
  funext g
  have h0 : crv x g 0 = g := by simp [crv]
  have hψc := hd_Dx x (dif (cd_ofReal hψ)) g
  set D := Dx x (fun g => ((ψ g : ℝ) : ℂ)) g with hDdef
  have hre : HasDerivAt (fun t => ψ (crv x g t)) D.re 0 := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hψc
    have hf : (⇑Complex.reCLM ∘ fun t => ((ψ (crv x g t) : ℝ) : ℂ)) = fun t => ψ (crv x g t) := by
      funext t; simp
    rw [hf] at this
    exact this.congr_deriv (by simp)
  have hD : D = (D.re : ℂ) := hψc.unique (by simpa using hre.ofReal_comp)
  have hit : HasDerivAt (iteratedDeriv q h) (iteratedDeriv (q + 1) h (ψ g)) (ψ (crv x g 0)) := by
    rw [h0, iteratedDeriv_succ]
    exact ((dif (cd_iter hh q)) (ψ g)).hasDerivAt
  have hcomp := (hit.comp (0 : ℝ) hre).ofReal_comp
  have hF := hd_Dx x (dif (cd_ofReal ((cd_iter hh q).comp hψ))) g
  have e1 : Dx x (fun g => ((iteratedDeriv q h (ψ g) : ℝ) : ℂ)) g
      = ((iteratedDeriv (q + 1) h (ψ g) * D.re : ℝ) : ℂ) := hF.unique hcomp
  rw [e1, Complex.ofReal_mul, ← hD]
end PI.UnitaryCorollaryDerivatives.CRH
