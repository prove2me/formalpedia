-- Prove2me | solution 1 for QEC.Coding.BDL26FirstReplacementSparseExactness.zero_slice_readout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:17:09.710533+00:00
-- url     : https://prove2.me/submissions/d11fc4e5-2369-4bc0-b0fd-1a005882b8a9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26FirstReplacementSparseExactness_sliceReadout_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstReplacementSparseExactness
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstReplacementSparseExactness
theorem _root_.solution (S : OddScale) (large : 16 ≤ S.half) (k : Fin 15) (w : W S)
    (zero : ∀ a : Atom S, w (atom S large k a)=0) : sliceReadout S large k w=0 := by
  rw [sliceReadout_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [show w (arm S large k b)=0 from zero (.inl b),zero_add]
  apply Finset.sum_eq_zero
  intro i _
  exact zero (.inr (b,i))
end QEC.Coding.BDL26FirstReplacementSparseExactness
