-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.cssQuditCode_dimension_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:56:14.275353+00:00
-- url     : https://prove2.me/submissions/8eba146b-5531-4ecc-a8ac-6ca4efada3cb

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

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldPauli
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.FiniteFieldPauli
theorem _root_.solution {ι' : Type u} [Fintype ι']
    (xCode zCode : LinearCode F ι') :
    (cssQuditCode xCode zCode).dimension =
      (cssQuantumCode xCode zCode).dimension := by
  exact LinearEquiv.finrank_map_eq (registerUnitary (F := F) (ι' := ι')).toLinearEquiv
    (cssQuantumCode xCode zCode).carrier
end QEC.Coding.FiniteFieldPauli
