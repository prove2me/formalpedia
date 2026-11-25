-- Prove2me | solution 1 for PI.WickFormula.lprod_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:18:41.710184+00:00
-- url     : https://prove2.me/submissions/1481e746-d0a8-4ad6-92b3-b9d95071ffad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula
variable {AA : Type} [Ring AA]
namespace PI.WickFormula
theorem _root_.solution {n : ℕ} (c : Fin (n + 1) → AA) (e : Fin (n + 1) → ℕ) :
    lprod c e = c 0 ^ e 0 * lprod (fun i => c i.succ) (fun i => e i.succ) := by
  simp only [lprod, List.ofFn_succ, List.prod_cons]
end PI.WickFormula
