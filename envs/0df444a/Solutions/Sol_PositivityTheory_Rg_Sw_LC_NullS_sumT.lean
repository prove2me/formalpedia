-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.sumT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:59:48.804443+00:00
-- url     : https://prove2.me/submissions/9d287b03-52ff-434f-8f04-35d5d040b41b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivQuadraticPairing
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SumPderivXMem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_sgn3
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_Qp_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.NullS
theorem _root_.solution (ε : Fin m → Bool) (p q : Prop) [Decidable p] [Decidable q] (k l : Fin n) :
    (∑ a, C (sgn ε a) * ((if p then C (sgn ε a) * X (a, l, false) else 0) *
      (if q then C (sgn ε a) * X (a, k, true) else 0)) : PX m n) = if p ∧ q then Qp ε k l else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp only [hp, hq, if_true, if_false, and_self, and_true, and_false,
    true_and, false_and, mul_zero, zero_mul, Finset.sum_const_zero]
  rw [Qp_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  linear_combination (X (a, k, true) * X (a, l, false) : PX m n) * sgn3 ε a
end PositivityTheory.Rg.Sw.LC.NullS
