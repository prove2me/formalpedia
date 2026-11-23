-- Prove2me | solution 1 for PI.Dv.HermitianFormEquivalence.asAlg_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:15.529266+00:00
-- url     : https://prove2.me/submissions/95634264-905f-4f23-a1b6-ce7cde3083a0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_ExistsSumEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.HermitianFormEquivalence
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.HermitianFormEquivalence
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V)
    (a : MonoidAlgebra K G) (x : V) : ρ.asAlgebraHom a x = ∑ g : G, a.coeff g • ρ g x := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply,
    Finsupp.sum_fintype _ _ (by intro g; simp)]
  simp [LinearMap.sum_apply]
end PI.Dv.HermitianFormEquivalence
