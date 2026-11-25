-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.cokernelLengthComparison_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:46:13.324333+00:00
-- url     : https://prove2.me/submissions/84a5db80-8838-4797-9bcb-4f907c41c6dc

import Definitions.Def_ReciprocityTheory_DualLattices_CokernelLengthComparisonStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Definitions.Def_ReciprocityTheory_DualLattices_CokernelLengthComparisonOf

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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hW1 : WdetLenStatement) (hW2 : WdetDegStatement) : CokernelLengthComparisonStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb
  obtain ⟨d, X, hd, hX, hXe⟩ :=
    hW1 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw cw cwb hcw hcwb
  have hle := hW2 p g C v R O σ cp hS H m e π he hσ h1 h2 h3 h4 w hw d X hd hX
  have hcp : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h5 := hS.cp_val
    rw [h0, zero_pow (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt).ne'] at h5
    exact hS.p_ne h5.symm
  have hpos : 0 < v (algebraMap R C cp) ^ d := pow_pos (pos_iff_ne_zero.mpr hcp) d
  have h6 : v (algebraMap R C cp) ^ d * cwb ≤ v (algebraMap R C cp) ^ d * cw := by
    rw [← hXe]
    exact mul_le_mul_of_nonneg_right hle zero_le
  exact le_of_mul_le_mul_left h6 hpos
end ReciprocityTheory.PGsh.Up
