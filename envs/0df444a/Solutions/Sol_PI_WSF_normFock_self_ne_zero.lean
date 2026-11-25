-- Prove2me | solution 1 for PI.WSF.normFock_self_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:11:58.537307+00:00
-- url     : https://prove2.me/submissions/6c9ab593-95e0-472a-b350-310bb4002197

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_CfEqSumOfSubset
import Theorems.Thm_PI_WSF_cf_F_ne
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockPos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WSF
open Formalism.BasicNotions MvPolynomial
namespace PI.WSF
theorem _root_.solution {N : ℕ} (lam : DomWeight N) (p : MvPolynomial (Fin N × Fin N) ℂ) (hp : p ≠ 0) :
    normFock lam p p ≠ 0 := by
  unfold normFock
  refine div_ne_zero ?_ (cf_F_ne lam)
  intro h0
  have h1 := (Formalism.GradedWeylDivisibility.fockPos _ p hp).1
  rw [h0, Complex.zero_re] at h1
  exact lt_irrefl _ h1
end PI.WSF
