-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.sum_mul_vecMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:36.415629+00:00
-- url     : https://prove2.me/submissions/66f6534c-60d1-4b3b-afaa-1955982c03c8

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_SumMulCommMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
variable {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
theorem _root_.solution {n : Type} [Fintype n] (A : Matrix n n E) (w : n → E) (c : n) :
    ∑ a, w a * A a c = (w ᵥ* A) c := by
  simp only [Matrix.vecMul, dotProduct]
end PI.UnitaryGroupMassFormula.FlagGramNonneg
