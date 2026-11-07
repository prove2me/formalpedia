-- Prove2me | solution 1 for QEC.Coding.FiniteFieldPauli.exists_dual_character_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:47:59.358997+00:00
-- url     : https://prove2.me/submissions/6a4f7177-239d-4368-95c9-18671e386064

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
import Theorems.Thm_QEC_Coding_FiniteFieldPauli_dual_dual_carrier_eq

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldPauli
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.FiniteFieldPauli
theorem _root_.solution (C : LinearCode F ι)
    (z : Word F ι) (hz : z ∉ C.carrier) :
    ∃ a : Word F ι, a ∈ C.dual.carrier ∧
      character F (wordPairing (F := F) (ι := ι) z a) ≠ 1 := by
  have hpair : ∃ a : Word F ι, a ∈ C.dual.carrier ∧
      wordPairing (F := F) (ι := ι) z a ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hdual : z ∈ C.dual.dual.carrier :=
      (C.dual.mem_dual z).2 hnone
    rw [dual_dual_carrier_eq] at hdual
    exact hz hdual
  obtain ⟨a, ha, hnonzero⟩ := hpair
  obtain ⟨t, ht⟩ := exists_character_mul_ne_one
    (wordPairing (F := F) (ι := ι) z a) hnonzero
  refine ⟨t • a, C.dual.carrier.smul_mem t ha, ?_⟩
  rw [map_smul, smul_eq_mul, mul_comm]
  exact ht
end QEC.Coding.FiniteFieldPauli
