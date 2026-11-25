-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PosPartIndep_proof_0995bedb399d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:25:20.452899+00:00
-- url     : https://prove2.me/submissions/4452eaac-48cf-4662-bb1c-2bfba7a79596

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_measurable_chartPosDens_47c1c9528926
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_isClosed_zeroSet_b1e5ce62660e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory ComplexSets Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace PosPartIndep
theorem _root_.solution (h : SheetOnlyNull.Statement) (hL : PosPartLocal.Statement)
    (hS : PosPartSplit.Statement) : PosPartIndep.Statement := by
  intro n d J A A' f φ hJ hd hA hA' hf hφ

  have key : ∀ x : Fin n → ℂ, ∃ W : Set (Fin n → ℂ), IsOpen W ∧
      ((∃ s, IsSheetAt J A x s) → (∃ s', IsSheetAt J A' x s') → x ∈ W) ∧
      ∀ E : Set (Fin n → ℂ), MeasurableSet E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (chartPosDens J A (E.indicator f) φ y) =
          ∫⁻ y, ENNReal.ofReal (chartPosDens J A' (E.indicator f) φ y) := by
    intro x
    by_cases hx : (∃ s, IsSheetAt J A x s) ∧ ∃ s', IsSheetAt J A' x s'
    · obtain ⟨W, hW, hxW, hWE⟩ := hL n d J A A' f φ x hf hφ hx.1 hx.2
      exact ⟨W, hW, fun _ _ => hxW, hWE⟩
    · refine ⟨∅, isOpen_empty, fun h1 h2 => absurd ⟨h1, h2⟩ hx, fun E _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.indicator_empty]
      simp [chartPosDens, sheetSum]
  choose W hWo hxW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E : ℕ → Set (Fin n → ℂ) := fun k => zeroSet J ∩ disjointed (fun k => W (e k)) k with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (SheetSumMeasurable.isClosed_zeroSet J).measurableSet.inter
      (MeasurableSet.disjointed (fun k => (hWo (e k)).measurableSet) k)
  have hEW : ∀ k, E k ⊆ W (e k) := fun k x hx => disjointed_subset (fun k => W (e k)) k hx.2
  have hEd : Pairwise (Function.onFun Disjoint E) := fun i j hij =>
    ((disjoint_disjointed (fun k => W (e k))) hij).mono Set.inter_subset_right
      Set.inter_subset_right
  have hcov : ∀ x ∈ zeroSet J, (∃ s, IsSheetAt J A x s) → (∃ s', IsSheetAt J A' x s') →
      ∃ k, x ∈ E k := by
    intro x hxZ h1 h2
    have : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x h1 h2⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    have : x ∈ ⋃ k, disjointed (fun k => W (e k)) k := by
      rw [iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hxi⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, hxZ, hk⟩

  have hae : ∀ B B' : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J B → IsFiniteProjection J B' →
      (∀ x ∈ zeroSet J, (∃ s, IsSheetAt J B x s) → (∃ s', IsSheetAt J B' x s') → ∃ k, x ∈ E k) →
      ∀ᵐ y, ENNReal.ofReal (chartPosDens J B f φ y) =
        ∑' k, ENNReal.ofReal (chartPosDens J B ((E k).indicator f) φ y) := by
    intro B B' hB hB' hc
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (h n d J B B' hJ hd hB hB')] with y hy
    refine hS n d J B f φ E y hB hEd fun x hx hs => hc x hx.1 hs ?_
    by_contra hn
    exact hy ⟨x, ⟨hx.1, hs, hn⟩, hx.2⟩
  have hint : ∀ B : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection J B →
      (∀ᵐ y, ENNReal.ofReal (chartPosDens J B f φ y) =
        ∑' k, ENNReal.ofReal (chartPosDens J B ((E k).indicator f) φ y)) →
      ∫⁻ y, ENNReal.ofReal (chartPosDens J B f φ y) =
        ∑' k, ∫⁻ y, ENNReal.ofReal (chartPosDens J B ((E k).indicator f) φ y) := by
    intro B hB hB2
    rw [lintegral_congr_ae hB2, lintegral_tsum fun k =>
      (IntegralIndep.measurable_chartPosDens hB (hf.indicator (hEm k)) φ).ennreal_ofReal.aemeasurable]
  rw [hint A hA (hae A A' hA hA' hcov),
    hint A' hA' (hae A' A hA' hA fun x hx h1 h2 => hcov x hx h2 h1)]
  exact tsum_congr fun k => hWE (e k) (E k) (hEm k) (hEW k)
end PosPartIndep
end GroundTheory.Heights₂.Heights
