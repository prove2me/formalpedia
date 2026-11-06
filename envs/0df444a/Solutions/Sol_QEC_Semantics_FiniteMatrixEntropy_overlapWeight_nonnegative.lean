-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.overlapWeight_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:48:28.896191+00:00
-- url     : https://prove2.me/submissions/9e6ab891-6b9d-4eaf-bfa0-024c76af742d

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.FiniteMatrixEntropy
namespace QEC.Semantics.FiniteMatrixEntropy
theorem _root_.solution {n : Type u} [Fintype n] [DecidableEq n]
    (U V : Matrix.unitaryGroup n Complex) (i j : n) :
    0 <= overlapWeight U V i j :=
  Complex.normSq_nonneg _
end QEC.Semantics.FiniteMatrixEntropy
