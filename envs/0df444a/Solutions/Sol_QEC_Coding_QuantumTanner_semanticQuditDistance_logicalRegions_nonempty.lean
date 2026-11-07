-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.semanticQuditDistance_logicalRegions_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:09:57.348104+00:00
-- url     : https://prove2.me/submissions/85b97f48-ae1e-40aa-94be-d5091c7f6ec3

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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_fullRegion_extension_surjective


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
    (hDistance : StabilizerCode.SemanticStabilizerDistance Q distance) :
    {weight : Nat |
      ∃ region : Semantics.QuditSubsystem (fun _ : iota => 2),
        Fintype.card region.SelectedCoordinates = weight ∧
          QEC.QLDPC.SupportsNondetectableLocalOperator Q.1.code region}.Nonempty := by
  obtain ⟨error, herror, _hweight, _hleast⟩ := hDistance
  let region : Semantics.QuditSubsystem (fun _ : iota => 2) :=
    Semantics.QuditSubsystem.fullRegion (fun _ : iota => 2)
  obtain ⟨localOperator, hlocal⟩ :=
    Semantics.QuditSubsystem.fullRegion_extension_surjective
      (fun _ : iota => 2) (fun _ => by decide)
      (PauliSymplectic.toQubitOperator error)
  refine ⟨Fintype.card region.SelectedCoordinates, region, rfl,
    localOperator, ?_⟩
  rw [hlocal]
  exact herror
end QEC.Coding.QuantumTanner
