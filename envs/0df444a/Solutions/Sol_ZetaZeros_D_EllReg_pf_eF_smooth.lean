-- Prove2me | solution 1 for ZetaZeros.D.EllReg.pf_eF_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:06:54.649434+00:00
-- url     : https://prove2.me/submissions/a432e863-9fd8-4faa-bc6b-ffe0bb800e48

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_PairingFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
private theorem exists_clm_eq_neg_two_pi_I_inner (ζ : E d) :
    ∃ L : E d →L[ℝ] ℂ, ∀ x, L x = -(2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ x ζ : ℝ) : ℂ)) := by
  refine ⟨(-(2 * (Real.pi : ℂ) * Complex.I)) • (Complex.ofRealCLM.comp (innerSL ℝ ζ)), fun x => ?_⟩
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  rw [innerSL_apply_apply, real_inner_comm]; ring
private theorem eF_eq_exp_comp_of_clm (ζ : E d) (L : E d →L[ℝ] ℂ)
    (hL : ∀ x, L x = -(2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ x ζ : ℝ) : ℂ))) :
    eF ζ = fun x => Complex.exp (L x) := by
  funext x; rw [hL]; rfl
end
end ZetaZeros.D.EllReg
end

set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
namespace ZetaZeros.D.EllReg
theorem _root_.solution (ξ : E d) : ContDiff ℝ ∞ (eF ξ) := by
  obtain ⟨L, hL⟩ := exists_clm_eq_neg_two_pi_I_inner ξ
  rw [eF_eq_exp_comp_of_clm ξ L hL]
  exact Complex.contDiff_exp.comp L.contDiff
end ZetaZeros.D.EllReg
