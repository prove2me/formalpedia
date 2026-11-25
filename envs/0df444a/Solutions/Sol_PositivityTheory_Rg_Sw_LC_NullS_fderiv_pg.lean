-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.fderiv_pg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:43:17.111868+00:00
-- url     : https://prove2.me/submissions/92a980e0-a807-4e4e-aa18-9dd5936da80c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PolyExpBound
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullOperatorEvaluation
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_hasFDerivAt_pg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.NullS
theorem _root_.solution (c : ℝ) (P : PX m n) (x v : Fin m → Fin n → ℂ) :
    fderiv ℝ (fun y => evX P y * gs c y) x v = evX (Qv c P v) x * gs c x := by
  rw [(hasFDerivAt_pg c P x).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, dP,
    ContinuousLinearMap.sum_apply, smul_eq_mul, Qv, evX, map_sum, map_add, map_mul, eval_C]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring
end PositivityTheory.Rg.Sw.LC.NullS
