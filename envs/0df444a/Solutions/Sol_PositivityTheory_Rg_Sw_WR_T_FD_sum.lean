-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.T.FD_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:31.468706+00:00
-- url     : https://prove2.me/submissions/78544c5c-63f0-4ba0-954e-993431ccce04

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_FD_cons
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_contDiff_FD
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_differentiable_of_top
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_Dkl_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.T
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.T
theorem _root_.solution {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → E n → ℂ) (hF : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (L : List (Fin n × Fin n)) : FD L (fun y => ∑ i ∈ s, c i * F i y) = fun y => ∑ i ∈ s, c i * FD L (F i) y := by
  induction L with
  | nil => rfl
  | cons kl L ih =>
    rw [FD_cons, ih]
    exact Dkl_sum s c (fun i => FD L (F i)) (fun i hi => differentiable_of_top (contDiff_FD (hF i hi) L)) _ _
end PositivityTheory.Rg.Sw.WR.T
