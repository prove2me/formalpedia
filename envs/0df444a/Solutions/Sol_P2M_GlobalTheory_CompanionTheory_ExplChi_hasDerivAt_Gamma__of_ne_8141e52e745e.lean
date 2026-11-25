-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_ExplChi_hasDerivAt_Gamma__of_ne_8141e52e745e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:50:26.545021+00:00
-- url     : https://prove2.me/submissions/247846c6-f7c0-40dc-890d-b5e90e369e3e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DirichletLogDerivReflectionFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExplChi
open Complex DirichletCharacter
namespace GlobalTheory.CompanionTheory.ExplChi
theorem _root_.solution {z : ℂ} (hz : ∀ n : ℕ, z / 2 ≠ -(n : ℂ)) :
    HasDerivAt Gammaℝ
      (Gammaℝ z * (-(Real.log Real.pi : ℂ) / 2 + digamma (z / 2) / 2)) z := by
  have hΓ : Gamma (z / 2) ≠ 0 := Gamma_ne_zero hz
  have hd : DifferentiableAt ℂ Gamma (z / 2) := differentiableAt_Gamma _ hz
  have h1 : HasDerivAt (fun w : ℂ => Gamma (w / 2)) (deriv Gamma (z / 2) * (1 / 2)) z :=
    hd.hasDerivAt.comp z ((hasDerivAt_id z).div_const 2)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      ((Real.pi : ℂ) ^ (-z / 2) * Complex.log Real.pi * (-1 / 2)) z :=
    ((hasDerivAt_id z).neg.div_const 2).const_cpow (Or.inl hpi)
  have h3 := h2.mul h1
  have hfun : Gammaℝ = fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Gamma (w / 2) := by
    funext w; rw [Gammaℝ_def]
  have hval : Gammaℝ z * (-(Real.log Real.pi : ℂ) / 2 + digamma (z / 2) / 2) =
      (Real.pi : ℂ) ^ (-z / 2) * Complex.log Real.pi * (-1 / 2) * Gamma (z / 2) +
        (Real.pi : ℂ) ^ (-z / 2) * (deriv Gamma (z / 2) * (1 / 2)) := by
    rw [Gammaℝ_def, digamma_def, logDeriv_apply, Complex.ofReal_log Real.pi_pos.le]
    field_simp
  rw [hval, hfun]
  exact h3
end GlobalTheory.CompanionTheory.ExplChi
