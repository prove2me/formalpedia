-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.card_binaryLowWeightWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:23:38.850538+00:00
-- url     : https://prove2.me/submissions/8218bd58-194d-4449-a807-c33be9b6a60d

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    (ι : Type v) [Fintype ι] [DecidableEq ι] (distance : Nat) :
    Fintype.card (BinaryLowWeightWords ι distance) =
      ∑ weight ∈ Finset.range distance,
        Nat.choose (Fintype.card ι) weight := by
  rw [Fintype.card_congr
      (binaryLowWeightWordsEquivSupports ι distance),
    Fintype.card_sigma, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro weight hweight
  rw [dif_pos (Finset.mem_range.mp hweight)]
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card,
    Nat.card_eq_fintype_card]
end QEC.Coding.QuantumTanner
