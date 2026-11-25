-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__continuous_vec_8c5d52ef9dc7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:29:42.482783+00:00
-- url     : https://prove2.me/submissions/3e900abc-1733-4b5c-94b5-3215b2d8d0ee

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneScalarPreservesNondegenerateStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureGeneralRankExtensionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂
theorem _root_.solution {K : Type} [TopologicalSpace K] [Zero K] {M n : ℕ} (u : K) (c : Fin n → K) :
    Continuous (fun X : Fin n → Fin M → K => vec u c X) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun a' => ?_) a
  · simp only [vec, Fin.cons_zero]; exact continuous_const
  · refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [vec, Fin.cons_succ, Fin.cons_zero]; exact continuous_const
    · simp only [vec, Fin.cons_succ]
      exact continuous_apply_apply a' i'
end GlobalTheory.CompanionTheory.SW.PiLocalization₂
