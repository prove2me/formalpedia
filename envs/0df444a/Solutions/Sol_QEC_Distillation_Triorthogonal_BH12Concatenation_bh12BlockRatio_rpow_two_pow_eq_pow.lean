-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Concatenation.bh12BlockRatio_rpow_two_pow_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:38:03.941231+00:00
-- url     : https://prove2.me/submissions/bfdb7c55-48c5-4667-8fbe-ee554223e7fc

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_one_lt_bh12BlockRatio
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology
namespace QEC.Distillation.Triorthogonal.BH12Concatenation
theorem _root_.solution {q : Nat} (hq : 0 < q)
    (z : Nat) :
    Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) =
      ((bh12InputCount q : ℝ) / bh12OutputCount q) ^ z := by
  calc
    Real.rpow ((2 : ℝ) ^ z) (bh12BlockExponent q) =
        Real.exp (Real.log ((2 : ℝ) ^ z) * bh12BlockExponent q) := by
      exact Real.rpow_def_of_pos (by positivity) _
    _ = Real.exp ((z : ℝ) * Real.log (bh12BlockRatio q)) := by
      unfold bh12BlockExponent
      congr 1
      rw [Real.log_pow]
      field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    _ = Real.rpow (bh12BlockRatio q) (z : ℝ) := by
      symm
      calc
        Real.rpow (bh12BlockRatio q) (z : ℝ) =
            Real.exp (Real.log (bh12BlockRatio q) * (z : ℝ)) :=
          Real.rpow_def_of_pos
            (lt_trans zero_lt_one (one_lt_bh12BlockRatio hq)) _
        _ = Real.exp ((z : ℝ) * Real.log (bh12BlockRatio q)) :=
          congrArg Real.exp (mul_comm _ _)
    _ = bh12BlockRatio q ^ z := Real.rpow_natCast _ _
    _ = ((bh12InputCount q : ℝ) / bh12OutputCount q) ^ z := rfl
end QEC.Distillation.Triorthogonal.BH12Concatenation
