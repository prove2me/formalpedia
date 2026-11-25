-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.sb_chi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:56.570654+00:00
-- url     : https://prove2.me/submissions/9b229393-ba78-4d2b-bc0d-aaa138194b55

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_IsOpenCoset
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_sb_mul
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_chi_lc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
variable [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}
variable (h : NADual V χ μ)
include h
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {φ : V → ℂ} (hφ : SB φ) (y : V) : SB fun x => φ x * χ x y := by
  simpa only [mul_comm, chi_sym h y] using sb_mul (chi_lc h y) hφ
end PositivityTheory.PlacePermOperatorBicommutantSpan
