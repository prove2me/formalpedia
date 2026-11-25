-- Prove2me | solution 1 for PI.QnCovLinW.ofFn_prod_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:21:31.327435+00:00
-- url     : https://prove2.me/submissions/2636fb90-ceb4-473f-848a-190258ea6f21

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
theorem _root_.solution {A : Type*} [Semiring A] {ι : Type*} [Fintype ι] :
    ∀ (t : ℕ) (f : Fin t → ι → A),
      (List.ofFn fun k => ∑ i, f k i).prod = ∑ c : Fin t → ι, (List.ofFn fun k => f k (c k)).prod
  | 0, f => by simp
  | t + 1, f => by
    simp only [List.ofFn_succ, List.prod_cons]
    rw [solution t (fun k => f k.succ), Finset.sum_mul_sum,
      ← (Fin.consEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type]
    simp [Fin.consEquiv]
end PI.QnCovLinW
