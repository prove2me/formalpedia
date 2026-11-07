-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.semanticStabilizerDistance_le_semanticQuditDistance_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:50:38.529727+00:00
-- url     : https://prove2.me/submissions/58520188-33d1-49f1-9bdc-5aae23d38345

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
import Theorems.Thm_QEC_Coding_QuantumTanner_semanticStabilizerDistance_le_card_of_nondetectable
import Theorems.Thm_QEC_QLDPC_semanticQuditDistance_attained


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    {iota : Type v} [Fintype iota] [DecidableEq iota]
    (Q : StabilizerCode.SourceValidBinary iota) {distance : Nat}
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q distance)
    (hnonempty : {weight : Nat |
      ∃ region : Semantics.QuditSubsystem
          (fun _ : iota => 2),
        Fintype.card region.SelectedCoordinates = weight ∧
          QEC.QLDPC.SupportsNondetectableLocalOperator Q.1.code region}.Nonempty) :
    distance ≤ QEC.QLDPC.semanticQuditDistance
      (fun _ : iota => 2) Q.1.code := by
  rcases QEC.QLDPC.semanticQuditDistance_attained Q.1.code hnonempty with
    ⟨region, hcard, hregion⟩
  rw [← hcard]
  exact semanticStabilizerDistance_le_card_of_nondetectable
    Q hDistance region hregion
end QEC.Coding.QuantumTanner
