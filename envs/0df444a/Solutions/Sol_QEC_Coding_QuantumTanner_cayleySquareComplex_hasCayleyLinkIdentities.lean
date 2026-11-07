-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.cayleySquareComplex_hasCayleyLinkIdentities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:23:05.341726+00:00
-- url     : https://prove2.me/submissions/1c67919b-e11e-4507-b264-a608a5be4a53

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
    {G A B : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
    (L : A → G) (R : B → G)
    (invA : Equiv.Perm A) (invB : Equiv.Perm B)
    (hL : Function.Injective L) (hR : Function.Injective R)
    (hLA : ∀ a, L (invA a) = (L a)⁻¹)
    (hRB : ∀ b, R (invB b) = (R b)⁻¹)
    (hTNC : ∀ g a b, L a * g ≠ g * R b) :
    (cayleySquareComplex L R invA invB hL hR hLA hRB hTNC).HasCayleyLinkIdentities := by
  constructor
  · intro g side a b
    apply Subtype.ext
    exact square_rebase_left L R invA hLA g side a b
  · intro g side a b
    apply Subtype.ext
    exact square_rebase_right L R invB hRB g side a b
end QEC.Coding.QuantumTanner
