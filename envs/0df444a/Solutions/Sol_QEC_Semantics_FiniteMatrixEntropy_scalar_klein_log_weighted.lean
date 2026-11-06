-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.scalar_klein_log_weighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:50:05.305387+00:00
-- url     : https://prove2.me/submissions/34b8beda-d64a-419b-a648-56644ea9fc45

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_scalar_klein_log

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.FiniteMatrixEntropy
namespace QEC.Semantics.FiniteMatrixEntropy
theorem _root_.solution {a b w : Real}
    (ha : 0 <= a) (hb : 0 < b) (hw : 0 <= w) :
    w * (a - b) <= w * (a * (Real.log a - Real.log b)) := by
  exact mul_le_mul_of_nonneg_left (scalar_klein_log ha hb) hw
end QEC.Semantics.FiniteMatrixEntropy
