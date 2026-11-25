-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.II.contDiff_xZx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:25.451602+00:00
-- url     : https://prove2.me/submissions/7d0cd195-c189-4902-bef1-2d46b353b871

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivXZxSkew
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_contDiff_entry
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_xZx_apply

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
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.II
theorem _root_.solution (Z : M2 n) (i j : Fin n ⊕ Fin n) : ContDiff ℝ ∞ (fun x : M2 n => (x * Z * xᴴ) i j) := by
  simp_rw [xZx_apply]
  refine ContDiff.sum fun l _ => ContDiff.mul (ContDiff.sum fun m _ => (contDiff_entry i m).mul contDiff_const) ?_
  exact Complex.conjCLE.contDiff.comp (contDiff_entry j l)
end PositivityTheory.Rg.Sw.LVs.II
