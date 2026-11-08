-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.Family.ofData_hasUniformLDPC_degreeSquared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:41:38.880271+00:00
-- url     : https://prove2.me/submissions/67041f05-e536-4d59-9ce8-44f842506155

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
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_boundaryIncidence_boundedLocality_degreeSquared
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_localityProfile

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
    (hcofinal : ∀ N : Nat, ∃ i, N ≤ (family i).blockLength)
    (Delta r : Nat)
    (hA : ∀ i, Fintype.card (A i) = Delta)
    (hB : ∀ i, Fintype.card (B i) = Delta)
    (hr : r ≤ Delta)
    (hCodeA : ∀ i, Dimension (family i).codeA = r)
    (hCodeB : ∀ i, Dimension (family i).codeB = Delta - r) :
    QEC.QLDPC.HasUniformLDPC (ofData family hcofinal) := by
  refine ⟨Delta * Delta, ?_⟩
  intro i
  rw [ofData_localityProfile]
  exact (family i).boundaryIncidence_boundedLocality_degreeSquared
    Delta r (hA i) (hB i) hr (hCodeA i) (hCodeB i)
end QEC.Coding.QuantumTanner.Family
