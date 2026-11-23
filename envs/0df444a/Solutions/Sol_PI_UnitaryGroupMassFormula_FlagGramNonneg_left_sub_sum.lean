-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.left_sub_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:40.123801+00:00
-- url     : https://prove2.me/submissions/85a864ea-8772-4d01-87e7-f995a74c7aee

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
    hT (z - ∑ a, c a • f a) x = hT z x - ∑ a, star (c a) * hT (f a) x := by
  simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]
end PI.UnitaryGroupMassFormula.FlagGramNonneg
