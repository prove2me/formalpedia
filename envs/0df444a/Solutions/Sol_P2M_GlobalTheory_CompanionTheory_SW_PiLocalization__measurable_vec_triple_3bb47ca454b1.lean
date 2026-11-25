-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__measurable_vec_triple_3bb47ca454b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:30:05.887663+00:00
-- url     : https://prove2.me/submissions/9784720b-ffa8-4ba5-9c26-8c2f7cb8267b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductFubini

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology ProbabilityTheory
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂
theorem _root_.solution {K : Type} [Zero K] [MeasurableSpace K] {M n : ℕ} :
    Measurable (fun p : K × (Fin n → K) × (Fin n → Fin M → K) =>
      (vec p.1 p.2.1 p.2.2 : Fin (n + 1) → Fin (M + 1) → K)) := by
  refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun i => ?_
  induction a using Fin.cases with
  | zero =>
    induction i using Fin.cases with
    | zero => simpa [vec] using measurable_fst
    | succ i => simpa [vec] using measurable_const
  | succ j =>
    induction i using Fin.cases with
    | zero =>
      simp only [vec, Fin.cons_succ, Fin.cons_zero]
      exact (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
    | succ i =>
      simp only [vec, Fin.cons_succ]
      exact (measurable_pi_apply i).comp
        ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
end GlobalTheory.CompanionTheory.SW.PiLocalization₂
