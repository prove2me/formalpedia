-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.isUnit_det_of_InG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:50.651163+00:00
-- url     : https://prove2.me/submissions/c2a769bb-3d1c-4e1e-96d5-4eb3f140819a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inv_of_InG

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
theorem _root_.solution {x : M2 n} (hx : InG x) : IsUnit x.det := by
  have h := congrArg Matrix.det (inv_of_InG hx)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact isUnit_iff_ne_zero.2 (fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h)
end PositivityTheory.Rg.Sw.LVs
