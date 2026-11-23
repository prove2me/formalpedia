-- Prove2me | solution 1 for P2M_GlobalTheory_hasDerivAt_canonicalSigma__ab13341749ec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:31.277866+00:00
-- url     : https://prove2.me/submissions/df4866e7-33c0-4217-87a2-aecfa7d6ed3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution (z : ℂ) : HasDerivAt (canonicalSigma L)
    ((deriv (weierstrassSigma L) z - sTwo L * z * weierstrassSigma L z) *
      cexp (-(sTwo L * z ^ 2 / 2))) z :=
  ((differentiable_weierstrassSigma L z).hasDerivAt.fun_mul
    ((((hasDerivAt_pow 2 z).const_mul (sTwo L)).div_const 2).fun_neg.cexp)).congr_deriv
    (by simp; ring)
end GlobalTheory
