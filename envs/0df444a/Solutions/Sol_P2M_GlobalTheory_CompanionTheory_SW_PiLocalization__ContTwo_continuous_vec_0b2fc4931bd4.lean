-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_continuous_vec_0b2fc4931bd4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:01:40.339798+00:00
-- url     : https://prove2.me/submissions/6b46a112-0c48-41f4-9463-e7887f064570

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GermFormPulledBackCombinationsExpandMonomials
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductUniqueness

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo
theorem _root_.solution {K : Type} [Zero K] [TopologicalSpace K] {M n : ℕ} :
    Continuous (fun p : K × (Fin n → K) × (Fin n → Fin M → K) => vec p.1 p.2.1 p.2.2) := by
  refine continuous_pi fun a => ?_
  refine Fin.cases ?_ (fun j => ?_) a
  · refine continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa [vec] using continuous_fst
    · simpa [vec] using continuous_const
  · refine continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun k => ?_) i
    · have h : Continuous (fun p : K × (Fin n → K) × (Fin n → Fin M → K) => p.2.1 j) :=
        (continuous_apply j).comp (continuous_fst.comp continuous_snd)
      simpa [vec] using h
    · have h : Continuous (fun p : K × (Fin n → K) × (Fin n → Fin M → K) => p.2.2 j k) :=
        (continuous_apply k).comp ((continuous_apply j).comp (continuous_snd.comp continuous_snd))
      simpa [vec] using h
end GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo
