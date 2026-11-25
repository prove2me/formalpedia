-- Prove2me | solution 1 for ZetaZeros.D.EllReg.iteratedPartialFourierChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:20:10.184379+00:00
-- url     : https://prove2.me/submissions/88d58fd0-d317-405a-941c-11a43484b24d

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_IteratedPartialFourierChar
import Theorems.Thm_ZetaZeros_D_EllReg_eF_eq_exp
import Theorems.Thm_ZetaZeros_D_EllReg_hasFDerivAt_eF
import Theorems.Thm_ZetaZeros_D_EllReg_eL_ev

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
namespace ZetaZeros.D.EllReg
theorem _root_.solution : DwExp := by
  intro d ξ w
  induction w with
  | nil => funext y; simp [dw]
  | cons j w ih =>
    funext x
    have hfun : dw w (eF ξ) =
        fun y => (w.map fun j => -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))).prod * eF ξ y := ih
    show fderiv ℝ (dw w (eF ξ)) x (ev j) = _
    rw [hfun, ((hasFDerivAt_eF ξ x).const_mul _).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, eL_ev, List.map_cons, List.prod_cons,
      eF_eq_exp]
    ring
end ZetaZeros.D.EllReg
