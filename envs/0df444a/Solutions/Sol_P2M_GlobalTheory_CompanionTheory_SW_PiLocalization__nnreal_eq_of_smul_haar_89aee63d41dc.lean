-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__nnreal_eq_of_smul_haar_89aee63d41dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:30:08.805823+00:00
-- url     : https://prove2.me/submissions/b5f80b00-38ed-4a07-bd1e-fe631846e54d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarModularCharacterOfContinuousAction
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RankOneFiberMeasureBlockExtension

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    {c e : ℝ≥0} (h : c • μ = e • μ) : c = e := by
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : V)
  have h1 : μ C ≠ ⊤ := hC.measure_lt_top.ne
  have h2 : μ C ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hC0).ne'
  have h3 : (c : ℝ≥0∞) * μ C = (e : ℝ≥0∞) * μ C := by
    have h' : (c • μ) C = (e • μ) C := by rw [h]
    rwa [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul,
      smul_eq_mul] at h'
  have h4 := (ENNReal.mul_left_inj h2 h1).1 h3
  exact_mod_cast h4
end GlobalTheory.CompanionTheory.SW.PiLocalization₂
