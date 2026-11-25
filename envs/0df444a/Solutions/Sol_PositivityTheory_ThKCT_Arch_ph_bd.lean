-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.ph_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:08:23.236587+00:00
-- url     : https://prove2.me/submissions/302b13ec-52bd-4e5e-b502-a007f8621588

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_u_smooth
import Theorems.Thm_PositivityTheory_ThKCT_Arch_u_deriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Arch
open scoped ContDiff NNReal
open Complex Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace PositivityTheory.ThKCT.Arch
theorem _root_.solution (l : V →L[ℝ] ℝ) (c : ℝ) (i : ℕ) (x : V) : ‖iteratedFDeriv ℝ i (ph l c) x‖ ≤ ‖l‖ ^ i := by
  have e := l.iteratedFDeriv_comp_right (u_smooth c) x (i := i) (by exact_mod_cast le_top)
  rw [show ph l c = (fun s : ℝ => cexp (I * ((s + c : ℝ) : ℂ))) ∘ l from rfl, e]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans (le_of_eq ?_)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, u_deriv, norm_mul, norm_pow, norm_I, one_pow, mul_comm I, norm_exp_ofReal_mul_I]
  simp
end PositivityTheory.ThKCT.Arch
