-- Prove2me | solution 1 for ZetaZeros.D.EllReg.Dec.dw_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:02:20.024967+00:00
-- url     : https://prove2.me/submissions/0fa26b1c-22d0-4921-bf17-8bc02d71ebb6

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
theorem _root_.solution {f g : E d → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : List (Fin d)) :
    dw w (fun y => f y + g y) = fun y => dw w f y + dw w g y := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    funext x
    show fderiv ℝ (dw w (fun y => f y + g y)) x (ev j) =
      fderiv ℝ (dw w f) x (ev j) + fderiv ℝ (dw w g) x (ev j)
    have h1 := (contDiff_dw hf w).differentiable (by simp) x
    have h2 := (contDiff_dw hg w).differentiable (by simp) x
    rw [ih]
    first
      | rw [show (fun y => dw w f y + dw w g y) = dw w f + dw w g from rfl, fderiv_add h1 h2]; rfl
      | rw [fderiv_fun_add h1 h2]; rfl
end ZetaZeros.D.EllReg.Dec
