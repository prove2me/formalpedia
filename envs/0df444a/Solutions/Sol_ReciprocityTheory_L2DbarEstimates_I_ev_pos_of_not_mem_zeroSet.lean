-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ev_pos_of_not_mem_zeroSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:57.099402+00:00
-- url     : https://prove2.me/submissions/2a0a58e6-2ff0-4c95-a2a2-627726662750

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocallyCompactSpaceOfIsLocalHomeomorph

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ)
    (r : ℝ) (hr : 0 < r) (x : M) (hx : x ∉ zeroSet n g) : 0 < ev n g ph r x := by
  simp only [zeroSet, Set.mem_ofPred_eq, not_forall] at hx
  obtain ⟨i, hi⟩ := hx
  have hs : 0 < ∑ i, ‖g i x‖ ^ 2 :=
    Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  exact div_pos (mul_pos hs (Real.exp_pos _)) (pow_pos hr 2)
end ReciprocityTheory.L2DbarEstimates.I
