-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.hasPositiveUniformProbability_iff_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:23:03.925231+00:00
-- url     : https://prove2.me/submissions/bd4de654-4923-4449-9310-9057c70555d1

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
    {Ω : Type u} [Fintype Ω] (event : Ω → Prop) [DecidablePred event] :
    HasPositiveUniformProbability event ↔ ∃ sample, event sample := by
  unfold HasPositiveUniformProbability
  constructor
  · intro hpositive
    obtain ⟨sample, hsample⟩ := Finset.card_pos.mp hpositive
    exact ⟨sample, (Finset.mem_filter.mp hsample).2⟩
  · rintro ⟨sample, hsample⟩
    apply Finset.card_pos.mpr
    exact ⟨sample, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsample⟩⟩
end QEC.Coding.QuantumTanner
