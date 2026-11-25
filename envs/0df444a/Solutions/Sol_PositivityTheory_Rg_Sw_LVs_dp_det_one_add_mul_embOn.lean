-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.dp_det_one_add_mul_embOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:04:08.839934+00:00
-- url     : https://prove2.me/submissions/51f17795-696e-4931-9888-33c66713e22b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_dp_embOn_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_proj_mul_mul_incl

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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) ℂ) (s : Finset (Fin n)) (T : Matrix s s ℂ) :
    (1 + M * embOn s T).det =
      (1 + M.submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n)) * T).det := by
  rw [dp_embOn_eq, ← Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc (proj s),
    proj_mul_mul_incl, Matrix.det_one_add_mul_comm]
end PositivityTheory.Rg.Sw.LVs
