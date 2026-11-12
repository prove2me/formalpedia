-- Prove2me | solution 1 for QEC.Coding.BDL26NativeSupportMetadata.atlas_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:17:36.691001+00:00
-- url     : https://prove2.me/submissions/c9bb933a-59e3-498f-b600-fb0435991756

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeStateRows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Theorems.Thm_QEC_Coding_BDL26NativeSupportMetadata_atlas_rows_cost

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeSupportMetadata
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open N
namespace QEC.Coding.BDL26NativeSupportMetadata
theorem _root_.solution (S : OddScale) (n : ℕ) :
    (atlasQ S n).operations≤(BDL26NativePresentationGenerator.setupQ S n).2+
      (T S n).length*(44*(T S n).length+2*(F S n).faces.length+132*(V S n).length+50)+2 ∧
    (atlasQ S n).allocations≤BDL26NativePresentationGenerator.allocatedRecords S n+
      (T S n).length*((T S n).length+3*(V S n).length+8)+1 := by
  have h := atlas_rows_cost (F S n) (V S n) (T S n)
  constructor
  · change (BDL26NativePresentationGenerator.setupQ S n).2+
      (atlasRowsQ (F S n) (V S n) (T S n)).operations+2≤_
    exact Nat.add_le_add_right (Nat.add_le_add_left h.1 _) 2
  · change BDL26NativePresentationGenerator.allocatedRecords S n+
      (atlasRowsQ (F S n) (V S n) (T S n)).allocations+1≤_
    exact Nat.add_le_add_right (Nat.add_le_add_left h.2 _) 1
end QEC.Coding.BDL26NativeSupportMetadata
