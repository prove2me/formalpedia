-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.registerUnitary_symm_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:49:08.09494+00:00
-- url     : https://prove2.me/submissions/e7b72a49-927f-4e82-a00c-498c589f07fc

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Coding_QLDPC_BPTMeasurementDistance
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.FieldTheory.Finiteness
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
import Theorems.Thm_QEC_Semantics_FiniteAlphabet_registerUnitary_apply_basis


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldPauli
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.FiniteFieldPauli
theorem _root_.solution
    {ι' : Type u} [Fintype ι'] (a : Word F ι') :
    (registerUnitary (F := F) (ι' := ι')).symm
        (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a)) =
      EuclideanSpace.basisFun _ Complex a := by
  change (registerUnitary (F := F) (ι' := ι')).toLinearEquiv.symm
    (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a)) = _
  apply (registerUnitary (F := F) (ι' := ι')).toLinearEquiv.injective
  rw [(registerUnitary (F := F) (ι' := ι')).toLinearEquiv.apply_symm_apply]
  exact (Semantics.FiniteAlphabet.registerUnitary_apply_basis F ι' a).symm
end QEC.Coding.FiniteFieldPauli
