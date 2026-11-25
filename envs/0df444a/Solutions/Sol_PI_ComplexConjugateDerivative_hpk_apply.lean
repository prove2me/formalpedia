-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.hpk_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:50.703472+00:00
-- url     : https://prove2.me/submissions/fe5be2a9-5dcb-4ee7-9889-9525275773a6

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open PI PI.ComplexConjugateDerivative
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
variable {k r : ℕ}
namespace PI.ComplexConjugateDerivative
theorem _root_.solution (i l : Fin (2 * r + k + 1)) :
    Hpk k r i l = if l.val = sgI k r i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hl := l.isLt
  simp only [Hpk, sgI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega | norm_num
end PI.ComplexConjugateDerivative
