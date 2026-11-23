-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DSIC.ofFn_prod_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:09.96794+00:00
-- url     : https://prove2.me/submissions/7c6906c9-7f88-4128-94a6-7fd65071894e

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
theorem _root_.solution {R : Type*} [Ring R] [Algebra ℂ R] :
    ∀ (t : ℕ) (a : Fin t → ℂ) (x : Fin t → R),
      (List.ofFn fun k => a k • x k).prod = (∏ k, a k) • (List.ofFn x).prod
  | 0, a, x => by simp
  | t + 1, a, x => by
    have h := solution t (fun i => a i.succ) (fun i => x i.succ)
    rw [List.ofFn_succ, List.prod_cons, h, List.ofFn_succ (f := x), List.prod_cons, Fin.prod_univ_succ,
      smul_mul_smul_comm]
end PI.UnitaryGroupMassFormula.DSIC
