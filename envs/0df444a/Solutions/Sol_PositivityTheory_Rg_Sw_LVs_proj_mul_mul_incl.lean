-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.proj_mul_mul_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:47:20.808743+00:00
-- url     : https://prove2.me/submissions/0a90d04b-8b44-42ca-a664-89903ddddca3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) :
    proj s * M * dp_incl s = M.submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n)) := by
  ext c d
  simp only [proj, dp_incl, Matrix.mul_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.submatrix_apply]
end PositivityTheory.Rg.Sw.LVs
