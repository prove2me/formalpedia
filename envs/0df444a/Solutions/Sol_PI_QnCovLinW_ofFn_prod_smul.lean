-- Prove2me | solution 1 for PI.QnCovLinW.ofFn_prod_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:07:41.22926+00:00
-- url     : https://prove2.me/submissions/1628ef2f-9417-4fbe-b701-cd4a01d36f2e

import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantLinearProduct_OfFnProdSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovLinW
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovLinW
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] :
    ∀ (t : ℕ) (r : Fin t → ℂ) (x : Fin t → A),
      (List.ofFn fun k => r k • x k).prod = (∏ k, r k) • (List.ofFn x).prod
  | 0, r, x => by simp
  | t + 1, r, x => by
    simp only [List.ofFn_succ, List.prod_cons]
    rw [solution t (fun k => r k.succ) (fun k => x k.succ), Fin.prod_univ_succ,
      smul_mul_smul_comm]
end PI.QnCovLinW
