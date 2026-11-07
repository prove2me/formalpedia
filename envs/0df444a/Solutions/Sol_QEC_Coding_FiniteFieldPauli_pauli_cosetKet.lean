-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.pauli_cosetKet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:53:21.955225+00:00
-- url     : https://prove2.me/submissions/c93fe33c-bfc9-4734-bc71-a4fcd62cfe07

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
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_phase_cosetKet_eigen
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_shift_cosetKet_translate

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldPauli
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.FiniteFieldPauli
theorem _root_.solution (xCode : LinearCode F ι)
    (x z a : Word F ι) (hz : z ∈ xCode.dual.carrier) :
    pauli x z (cosetKet xCode a) =
      (character F (wordPairing (F := F) (ι := ι) z a)) •
        cosetKet xCode (a - x) := by
  rw [pauli, Module.End.mul_apply, phase_cosetKet_eigen xCode z a hz,
    map_smul, shift_cosetKet_translate]
end QEC.Coding.FiniteFieldPauli
