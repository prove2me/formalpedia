-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_scalarLinearInt__9d6bbd947da1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:38:56.388253+00:00
-- url     : https://prove2.me/submissions/8396b8a0-c4d5-4117-bd2e-0e70c879340c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
import Theorems.Thm_Formalism_L2_Th1_C_Clo_endInt_natCast
import Theorems.Thm_Formalism_L2_Th1_C_Clo_addDefect_zero_right
import Theorems.Thm_Formalism_L2_Th1_C_Clo_addDefect_add_right
import Theorems.Thm_Formalism_L2_Th1_C_Clo_zLin_natCast
import Theorems.Thm_Formalism_L2_Th1_C_Pts_endInt_neg
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fadd_fmul_neg
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_fmul
import Theorems.Thm_Formalism_L2_Th1_C_lGSubgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Clo
namespace Formalism.L2.Th1.C
theorem _root_.solution : ZLinInt := by
  intro K _ _ R l linv ph h h1 n σ x y hx hy
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [Int.cast_natCast]
    exact zLin_natCast h h1 hx hy m
  · rw [Int.cast_neg, Int.cast_natCast]
    have hm := endInt_natCast (R := R) h.1 h.2.1 m
    have hp := addDefect_add_right h1 hx (Pts.isPt_fmul h.1 hm hy)
      (Pts.isPt_fmul h.1 (Pts.endInt_neg h.1 h.2.1 hm) hy)
    rw [Pts.fadd_fmul_neg h.1 _ hy.1, addDefect_zero_right h hx.1] at hp
    have := (lGSubgroup K R σ).2.2 _
      ((lGSubgroup K R σ).2.1 _ _ hp (zLin_natCast h h1 hx hy m))
    unfold Cong
    rw [neg_smul]
    convert this using 1
    abel
end Formalism.L2.Th1.C
