-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DSIC.ofFn_prod_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:53.411681+00:00
-- url     : https://prove2.me/submissions/1cce0c60-14d9-412d-99df-931f49595495

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_CentralScalar
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QuasiDeterminantConjInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DSIC
open Finset
open scoped Matrix
namespace PI.UnitaryGroupMassFormula.DSIC
theorem _root_.solution {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ (t : ℕ) (f : Fin t → ι → R),
      (List.ofFn fun k => ∑ c, f k c).prod = ∑ c : Fin t → ι, (List.ofFn fun k => f k (c k)).prod
  | 0, f => by simp
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, solution t, Finset.sum_mul_sum,
      ← (Fin.consEquiv fun _ : Fin (t + 1) => ι).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    simp [List.ofFn_succ, Fin.consEquiv]
end PI.UnitaryGroupMassFormula.DSIC
