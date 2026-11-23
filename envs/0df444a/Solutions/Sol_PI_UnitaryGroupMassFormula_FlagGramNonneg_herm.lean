-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:25:54.246255+00:00
-- url     : https://prove2.me/submissions/38707fbf-c8c3-4147-a33b-2a3b4b9f921a

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
theorem _root_.solution {hT : V →ₗ⋆[E] V →ₗ[E] E} (hS : hT.IsSymm) (x y : V) : hT x y = star (hT y x) := by
  first
    | exact (hS.eq y x).symm
    | exact (hS y x).symm
end PI.UnitaryGroupMassFormula.FlagGramNonneg
