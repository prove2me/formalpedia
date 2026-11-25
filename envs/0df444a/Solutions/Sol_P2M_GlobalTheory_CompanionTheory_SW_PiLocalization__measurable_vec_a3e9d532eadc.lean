-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__measurable_vec_a3e9d532eadc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:30:02.933293+00:00
-- url     : https://prove2.me/submissions/78b07bcc-0843-48b8-85d9-469ce59f9403

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductMeasurableStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductNormalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂
theorem _root_.solution {K : Type} [Zero K] [MeasurableSpace K] {M n : ℕ} (α : K) (c : Fin n → K) :
    Measurable (fun X : Fin n → Fin M → K => vec α c X) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
  induction i using Fin.cases with
  | zero => simpa [vec] using (measurable_const : Measurable fun _ : Fin n → Fin M → K =>
      (Fin.cons α (fun _ => 0) : Fin (M + 1) → K) k)
  | succ i =>
    induction k using Fin.cases with
    | zero => simpa [vec] using (measurable_const : Measurable fun _ : Fin n → Fin M → K => c i)
    | succ k =>
      have h : Measurable fun X : Fin n → Fin M → K => X i k :=
        (measurable_pi_apply k).comp (measurable_pi_apply i)
      simpa [vec] using h
end GlobalTheory.CompanionTheory.SW.PiLocalization₂
