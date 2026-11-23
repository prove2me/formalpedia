-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LVs_continuousOn_inv__7715fb95dd1b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:53.700552+00:00
-- url     : https://prove2.me/submissions/1e3987f8-856f-4984-a5ff-2abdc1800979

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {m : Type} [Fintype m] [DecidableEq m] :
    ContinuousOn (fun x : Matrix m m ℂ => x⁻¹) {x | x.det ≠ 0} := by
  have h : ContinuousOn (fun x : Matrix m m ℂ => (x.det)⁻¹ • x.adjugate) {x | x.det ≠ 0} :=
    ((continuous_id.matrix_det).continuousOn.inv₀ fun x hx => hx).smul continuous_id.matrix_adjugate.continuousOn
  refine h.congr fun x hx => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
end PositivityTheory.Rg.Sw.LVs
