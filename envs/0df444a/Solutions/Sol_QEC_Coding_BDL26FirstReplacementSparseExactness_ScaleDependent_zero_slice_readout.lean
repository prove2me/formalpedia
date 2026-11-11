-- Prove2me | solution 1 for QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent.zero_slice_readout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:39:02.969209+00:00
-- url     : https://prove2.me/submissions/05c74ec2-6d9d-4ba4-872a-3889e2a42bf1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_sliceReadout_apply
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_ScaleDependent_sliceReadout_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
theorem _root_.solution (S : OddScale) (n : Nat) (large : n+2 ≤ S.half) (k : Fin (n+1)) (w : W S)
    (zero : ∀ a : Atom S, w (atom S n large k a)=0) : sliceReadout S n large k w=0 := by
  rw [sliceReadout_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [show w (arm S n large k b)=0 from zero (.inl b),zero_add]
  apply Finset.sum_eq_zero
  intro i _
  exact zero (.inr (b,i))
end QEC.Coding.BDL26FirstReplacementSparseExactness.ScaleDependent
