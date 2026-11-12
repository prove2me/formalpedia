-- Prove2me | solution 1 for QEC.Distillation.HH18.HH18BinomialTailAsymptotics.binomialTail_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:37:49.505959+00:00
-- url     : https://prove2.me/submissions/4171d09d-3ce6-4414-9331-95abb8b36be2

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_ParameterSequence
import Mathlib.Analysis.SpecialFunctions.Stirling
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Sublogarithmic_BinomialTailAsymptotics

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.HH18 QEC.Distillation.HH18.HH18BinomialTailAsymptotics
open Coding.PuncturedReedMuller
open Filter Topology
namespace QEC.Distillation.HH18.HH18BinomialTailAsymptotics
theorem _root_.solution (n w : Nat) : binomialTail n w ≤ 2 ^ n := by
  unfold binomialTail
  calc
    ∑ i ∈ Finset.Icc (w + 1) n, Nat.choose n i ≤
        ∑ i ∈ Finset.range (n + 1), Nat.choose n i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_Icc.mp hi).2)
      · intro _ _ _
        exact Nat.zero_le _
    _ = 2 ^ n := Nat.sum_range_choose n
end QEC.Distillation.HH18.HH18BinomialTailAsymptotics
