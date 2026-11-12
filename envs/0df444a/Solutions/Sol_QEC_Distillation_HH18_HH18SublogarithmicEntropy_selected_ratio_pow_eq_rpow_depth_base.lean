-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18SublogarithmicEntropy.selected_ratio_pow_eq_rpow_depth_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:14:32.486205+00:00
-- url     : https://prove2.me/submissions/b6140021-f4c4-4a46-81f4-e3e67d2db30b

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_TargetSchedule
import Theorems.Thm_QEC_Distillation_HH18_HH18SublogarithmicEntropy_selected_parameter_counts_nontrivial
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

section
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology
private theorem ratio_pow_eq_rpow_depth_base {n k d z : Nat}
    (hn : 0 < n) (hk : 0 < k) (hd : 1 < d) :
    ((n : ℝ) / k) ^ z =
      Real.rpow ((d : ℝ) ^ z) (concatenationExponent n k d) := by
  have hratio : 0 < (n : ℝ) / k := by
    exact div_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hk)
  have hdReal : 1 < (d : ℝ) := by exact_mod_cast hd
  have hdPos : 0 < (d : ℝ) := lt_trans zero_lt_one hdReal
  have hbase : 0 < (d : ℝ) ^ z := pow_pos hdPos _
  have hlogd : 0 < Real.log d := Real.log_pos hdReal
  calc
    ((n : ℝ) / k) ^ z = Real.rpow ((n : ℝ) / k) (z : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ = Real.exp (Real.log ((n : ℝ) / k) * (z : ℝ)) :=
      Real.rpow_def_of_pos hratio _
    _ = Real.exp
        (Real.log ((d : ℝ) ^ z) * concatenationExponent n k d) := by
      congr 1
      rw [Real.log_pow]
      unfold concatenationExponent
      field_simp [ne_of_gt hlogd]
    _ = Real.rpow ((d : ℝ) ^ z) (concatenationExponent n k d) :=
      (Real.rpow_def_of_pos hbase _).symm
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
end

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18SublogarithmicEntropy
open Coding.PuncturedReedMuller
open Coding.ReedMuller
open Filter Topology
namespace QEC.Distillation.HH18.HH18SublogarithmicEntropy
theorem _root_.solution (A D j z : Nat)
    (hD : 0 < D) (hwindow : 3 * A < D) (hj : 0 < j) :
    ((parameterLength A D j : ℝ) / parameterDimension A D j) ^ z =
      Real.rpow ((parameterDistance A D j : ℝ) ^ z)
        (concatenationExponent (parameterLength A D j)
          (parameterDimension A D j) (parameterDistance A D j)) := by
  rcases selected_parameter_counts_nontrivial A D j hD hwindow hj with
    ⟨hn, hk, hd⟩
  exact ratio_pow_eq_rpow_depth_base hn hk hd
end QEC.Distillation.HH18.HH18SublogarithmicEntropy
