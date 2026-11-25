-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_cpow_step_le__738caad9bd19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:42.168803+00:00
-- url     : https://prove2.me/submissions/a4129ed2-f289-4248-a89d-9f9987c95a3b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensPair
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_cpow_neg_sub_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution {i U : ℕ} (hU : 1 ≤ U) (hi : U ≤ i) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖(((i + 1 : ℕ) : ℂ) ^ (-w) - (i : ℂ) ^ (-w))‖ ≤ ‖w‖ / U := by
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (by omega : 1 ≤ i)
  have h := norm_cpow_neg_sub_le (a := i) (b := (i : ℝ) + 1) hi1 (by linarith) hw
  have e1 : (((i : ℝ) : ℂ)) = (i : ℂ) := by push_cast; rfl
  have e2 : ((((i : ℝ) + 1 : ℝ)) : ℂ) = ((i + 1 : ℕ) : ℂ) := by push_cast; rfl
  rw [e1, e2] at h
  refine h.trans ?_
  have hUi : (U : ℝ) ≤ i := by exact_mod_cast hi
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have : ((i : ℝ) + 1 - i) / i ≤ 1 / U := by
    rw [add_sub_cancel_left]
    exact one_div_le_one_div_of_le hU0 hUi
  calc ‖w‖ * (((i : ℝ) + 1 - i) / i) ≤ ‖w‖ * (1 / U) :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = ‖w‖ / U := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
