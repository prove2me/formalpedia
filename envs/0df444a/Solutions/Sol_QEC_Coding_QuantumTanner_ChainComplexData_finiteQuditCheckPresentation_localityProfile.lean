-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.ChainComplexData.finiteQuditCheckPresentation_localityProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:49:32.981948+00:00
-- url     : https://prove2.me/submissions/88896cd6-73f2-427e-9687-e78d2e354b62

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
import Theorems.Thm_QEC_Coding_QuantumTanner_ChainComplexData_finiteQuditCheckPresentation_incidence

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
open scoped TensorProduct
universe u v
open QEC.Coding.QuantumTanner.ChainComplexData
namespace QEC.Coding.QuantumTanner.ChainComplexData
theorem _root_.solution
    {iota kappa lambda : Type v}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [Fintype lambda]
    (K : ChainComplexData
      (ZMod 2) (Word (ZMod 2) kappa) (Word (ZMod 2) iota)
        (Word (ZMod 2) lambda))
    (encodedQudits : Nat)
    (hdimension :
      Module.finrank Complex (K.binaryCSSCode).stabilizer.code.carrier =
        2 ^ encodedQudits) :
    (finiteQuditCheckPresentation K encodedQudits hdimension).localityProfile =
      (QEC.QLDPC.chainComplexBoundaryIncidence K).localityProfile := by
  change
    (finiteQuditCheckPresentation K encodedQudits hdimension).incidence.localityProfile =
      (QEC.QLDPC.chainComplexBoundaryIncidence K).localityProfile
  rw [finiteQuditCheckPresentation_incidence]
end QEC.Coding.QuantumTanner.ChainComplexData
