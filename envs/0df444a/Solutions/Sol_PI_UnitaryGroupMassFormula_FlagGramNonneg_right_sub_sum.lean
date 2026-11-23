-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.right_sub_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:25:35.378077+00:00
-- url     : https://prove2.me/submissions/c7b38914-b2b9-41bc-9490-b6c992e5f195

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
theorem _root_.solution (hT : V →ₗ⋆[E] V →ₗ[E] E) {ι : Type} [Fintype ι] (z : V) (c : ι → E)
    (f : ι → V) (x : V) :
    hT x (z - ∑ a, c a • f a) = hT x z - ∑ a, c a * hT x (f a) := by
  simp only [map_sub, map_sum, map_smul, smul_eq_mul]
end PI.UnitaryGroupMassFormula.FlagGramNonneg
