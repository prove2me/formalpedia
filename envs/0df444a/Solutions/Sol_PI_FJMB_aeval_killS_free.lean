-- Prove2me | solution 1 for PI.FJMB.aeval_killS_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:38.089663+00:00
-- url     : https://prove2.me/submissions/bb97ec76-eb00-4708-ac62-1c8b0592f2c5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurDiag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurCauchy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
namespace PI.FJMB
theorem _root_.solution {S : Set σ} {Q : MvPolynomial σ ℂ} (h : ∀ e ∈ Q.support, ∀ v ∈ S, e v = 0) :
    aeval (killS S) Q = Q := by
  conv_rhs => rw [Q.as_sum]
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [aeval_monomial, monomial_eq, Finsupp.prod, Finsupp.prod, algebraMap_eq]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  have hvS : v ∉ S := fun hvS => (Finsupp.mem_support_iff.mp hv) (h e he v hvS)
  simp only [killS, if_neg hvS]
end PI.FJMB
