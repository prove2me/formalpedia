-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__ContTwo_continuous_tl_6db6ebf34396
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:01:29.998983+00:00
-- url     : https://prove2.me/submissions/161b5b1b-2290-45ba-9c61-750ea806ee33

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
theorem _root_.solution {K : Type} [TopologicalSpace K] {M n : ℕ} :
    Continuous (tl : (Fin (n + 1) → Fin (M + 1) → K) → Fin n → Fin M → K) := by
  refine continuous_pi fun j => continuous_pi fun i => ?_
  exact (continuous_apply i.succ).comp (continuous_apply j.succ)
end GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo
