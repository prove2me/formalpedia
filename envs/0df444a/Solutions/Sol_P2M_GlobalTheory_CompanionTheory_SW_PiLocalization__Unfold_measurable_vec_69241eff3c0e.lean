-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Unfold_measurable_vec_69241eff3c0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:29:30.542951+00:00
-- url     : https://prove2.me/submissions/9f72b03c-e845-440f-8255-44f856a9d88e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerate
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductUnfoldStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductFoldStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductDensity

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold
theorem _root_.solution {K : Type} [Zero K] [MeasurableSpace K] {M n : ℕ} (α : K) :
    Measurable (fun p : (Fin n → K) × (Fin n → Fin M → K) => vec α p.1 p.2) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp only [vec, Fin.cons_zero]
    exact measurable_const
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simp only [vec, Fin.cons_succ, Fin.cons_zero]
      exact (measurable_pi_apply i').comp measurable_fst
    · simp only [vec, Fin.cons_succ]
      exact (measurable_pi_apply j').comp ((measurable_pi_apply i').comp measurable_snd)
end GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold
