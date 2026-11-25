-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.sum_mul_comm_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:33.085478+00:00
-- url     : https://prove2.me/submissions/95265b2d-6cc3-4bdd-b5ca-4269c65687ae

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
    ∑ b, w b * A c b = (A *ᵥ w) c := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _
end PI.UnitaryGroupMassFormula.FlagGramNonneg
