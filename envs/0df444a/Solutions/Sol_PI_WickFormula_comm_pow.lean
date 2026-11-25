-- Prove2me | solution 1 for PI.WickFormula.comm_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:25:38.246099+00:00
-- url     : https://prove2.me/submissions/e2198ec2-4bf6-4768-9892-dbb5ece0b55b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_LprodAddSmul
import Theorems.Thm_PI_WickFormula_comm_pow_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula
variable {k AA : Type} [CommRing k] [Ring AA] [Algebra k AA]
namespace PI.WickFormula
theorem _root_.solution (b c : AA) (t : k) (h : b * c = c * b + algebraMap k AA t) (n : ℕ) :
    b * c ^ n = c ^ n * b + ((n : k) * t) • c ^ (n - 1) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [comm_pow_succ b c t h m]
    simp
end PI.WickFormula
