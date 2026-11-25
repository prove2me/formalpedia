-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.delta_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:03:58.013086+00:00
-- url     : https://prove2.me/submissions/f379a5d4-8a21-4f2f-a2b7-d82704384091

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_word

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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
open PositivityTheory.Rg.Sw.WR.K.GB.TW
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB.TW
theorem _root_.solution (z : ℂ) (c : ℕ → E n → ℂ) (M : ℕ) (hc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j))
    (hM : ∀ j, M ≤ j → c j = 0) :
    Delta (fun y => W z y * ∑ j ∈ Finset.range M, z ^ j * c j y) =
      fun y => W z y * ∑ j ∈ Finset.range (M + n), z ^ j * TDelta c j y := by
  funext y
  unfold Delta
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [word z _ (List.finRange n) c M hc hM, List.length_finRange]
  simp only [TDelta, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σ _ => by ring
end PositivityTheory.Rg.Sw.WR.K.GB.TW
