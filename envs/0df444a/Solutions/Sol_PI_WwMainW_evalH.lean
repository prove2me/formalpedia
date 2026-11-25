-- Prove2me | solution 1 for PI.WwMainW.evalH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:39:55.404896+00:00
-- url     : https://prove2.me/submissions/5fda49bd-5c20-4617-ad00-df64c6b81b3d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_LfunEqOfSubset
import Theorems.Thm_PI_WwMainW_chi_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open PI PI.WwMainW
open PI.WwMain PI.WwMain.KM
namespace PI.WwMainW
theorem _root_.solution : EvalH := by
  unfold EvalH Hpol
  intro Lt _ _ l _ N0 N1 ph G z
  conv_rhs => rw [G.as_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [chi_monomial, MvPolynomial.eval_monomial, MvPolynomial.C_mul', map_smul, smul_eq_mul]
  ring
end PI.WwMainW
