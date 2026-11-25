-- Prove2me | solution 1 for ZetaZeros.D.EllReg.Dec.dw_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:00:17.243477+00:00
-- url     : https://prove2.me/submissions/ca86cb3b-b6a5-4217-ace5-dfb58a4b29ce

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_Decompose
import Theorems.Thm_ZetaZeros_D_EllReg_Dec_contDiff_dw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
open ZetaZeros.D.EllReg.Dec
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.Dec
theorem _root_.solution {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) (c : ℂ) (w : List (Fin d)) :
    dw w (fun y => c * f y) = fun y => c * dw w f y := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    funext x
    show fderiv ℝ (dw w (fun y => c * f y)) x (ev j) = c * fderiv ℝ (dw w f) x (ev j)
    have h1 := (contDiff_dw hf w).differentiable (by simp) x
    rw [ih]
    first
      | rw [fderiv_const_mul h1]; simp
      | rw [fderiv_fun_const_mul h1]; simp
      | rw [show (fun y => c * dw w f y) = c • dw w f from rfl, fderiv_const_smul h1]; simp
end ZetaZeros.D.EllReg.Dec
