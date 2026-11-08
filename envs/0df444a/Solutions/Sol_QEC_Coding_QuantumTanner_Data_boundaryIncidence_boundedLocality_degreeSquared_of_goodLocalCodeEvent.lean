-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Data.boundaryIncidence_boundedLocality_degreeSquared_of_goodLocalCodeEvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:40:48.086776+00:00
-- url     : https://prove2.me/submissions/7b89c626-978c-4e21-9ed6-62797de6681c

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
import Theorems.Thm_QEC_Coding_QuantumTanner_dimension_codeA_of_goodLocalCodeEvent
import Theorems.Thm_QEC_Coding_QuantumTanner_dimension_codeB_of_goodLocalCodeEvent
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_boundaryIncidence_boundedLocality_degreeSquared

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
open QEC.Coding.QuantumTanner.Data
variable {G A B Square XBasis ZBasis : Type v}
variable [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
variable [Fintype XBasis] [Fintype ZBasis]
namespace QEC.Coding.QuantumTanner.Data
theorem _root_.solution
    (D : Data G A B Square XBasis ZBasis)
    {Delta r distanceThreshold robustness punctures : Nat}
    (sample : RandomLocalCodeSample r A B)
    (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hr : r ≤ Delta)
    (hCodeA : D.codeA = sample.codeA)
    (hCodeB : D.codeB = sample.codeB)
    (hgood : GoodLocalCodeEvent
      r (Delta - r) distanceThreshold robustness punctures sample) :
    QEC.Coding.BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence D.chainComplex).localityProfile
      (Delta * Delta) := by
  apply D.boundaryIncidence_boundedLocality_degreeSquared Delta r hA hB hr
  · rw [hCodeA]
    exact dimension_codeA_of_goodLocalCodeEvent hgood
  · rw [hCodeB]
    exact dimension_codeB_of_goodLocalCodeEvent hgood
end QEC.Coding.QuantumTanner.Data
