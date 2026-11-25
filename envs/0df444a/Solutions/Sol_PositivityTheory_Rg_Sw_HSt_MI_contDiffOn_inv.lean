-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.MI.contDiffOn_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:47:41.270368+00:00
-- url     : https://prove2.me/submissions/8a94c8ab-31df-472c-9cc7-41d73de61887

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_MatInv
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_MI_contDiff_det
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_MI_contDiff_adjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Set Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.MI
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.HSt.MI
theorem _root_.solution : ContDiffOn ℝ ∞ (fun x : M2 n => x⁻¹) (Inv n) := by
  have hd : ContDiffOn ℝ ∞ (fun x : M2 n => (x.det)⁻¹) (Inv n) :=
    contDiff_det.contDiffOn.inv fun x hx => hx
  have : ContDiffOn ℝ ∞ (fun x : M2 n => (x.det)⁻¹ • x.adjugate) (Inv n) := hd.smul contDiff_adjugate.contDiffOn
  refine this.congr fun x hx => ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
end PositivityTheory.Rg.Sw.HSt.MI
