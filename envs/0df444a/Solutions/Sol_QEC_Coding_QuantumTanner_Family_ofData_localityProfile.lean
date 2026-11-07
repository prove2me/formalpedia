-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Family.ofData_localityProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:08:06.094601+00:00
-- url     : https://prove2.me/submissions/33b7cfc5-3ed9-459f-8c0b-1dc3e58a9a3e

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
import Theorems.Thm_QEC_Coding_QuantumTanner_ChainComplexData_finiteQuditCheckPresentation_localityProfile
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_finiteQuditCheckPresentation_localityProfile

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
open QEC.Coding.QuantumTanner.Family
variable {Index : Type u}
variable {G A B Square XBasis ZBasis : Index → Type v}
variable [∀ i, Group (G i)] [∀ i, Fintype (G i)]
variable [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
variable [∀ i, Fintype (Square i)] [∀ i, DecidableEq (Square i)]
variable [∀ i, Fintype (XBasis i)] [∀ i, Fintype (ZBasis i)]
namespace QEC.Coding.QuantumTanner.Family
theorem _root_.solution
    (family : ∀ i, Data (G i) (A i) (B i) (Square i) (XBasis i) (ZBasis i))
    (hcofinal : ∀ N : Nat, ∃ i, N ≤ (family i).blockLength) (i : Index) :
    (ofData family hcofinal).localityProfile i =
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (family i).chainComplex).localityProfile := by
  exact (family i).finiteQuditCheckPresentation_localityProfile
end QEC.Coding.QuantumTanner.Family
