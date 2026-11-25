-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatChartChangeVar_posPart_eq_457a933ba476
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:40:15.950189+00:00
-- url     : https://prove2.me/submissions/204558f5-4ce3-48ea-8f02-86507e2e6c37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatChartChangeVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSheetNoRatNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatChartChangeVar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatChartChangeVar_measurable_ratPosDens_6e6772a3a708
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratPosDens_split_c1d7b98829fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_measurable_chartPosDens_47c1c9528926
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_proof_4b5bf5e5d261
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PosPartSplit_proof_e6248afef178
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_isClosed_zeroSet_b1e5ce62660e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets
open GroundTheory.Heights₂.Heights.RatChartChangeVar
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.RatChartChangeVar
theorem _root_.solution (hM : RatSheetSumMeasurable.Statement) (hN1 : RatSheetNoChartNull.Statement)
    (hN2 : ChartSheetNoRatNull.Statement) (hL : RatPosPartLocal.Statement)
    {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ}
    {f : (Fin n → ℂ) → ℝ} {φ : Fin d → (Fin n → ℂ) → ℝ}
    (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hA : IsFiniteProjection J A)
    (hq : q ∉ J) (hfin : ∀ y, (RatChart.ratFibre J p q y).Finite) (hf : Measurable f)
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k)) :
    ∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y) =
      ∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y) := by

  have key : ∀ x : Fin n → ℂ, ∃ W : Set (Fin n → ℂ), IsOpen W ∧
      ((∃ s, IsSheetAt J A x s) → (∃ s', RatChart.IsRatSheetAt J p q x s') → x ∈ W) ∧
      ∀ E : Set (Fin n → ℂ), MeasurableSet E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q (E.indicator f) φ y) =
          ∫⁻ y, ENNReal.ofReal (chartPosDens J A (E.indicator f) φ y) := by
    intro x
    by_cases hx : (∃ s, IsSheetAt J A x s) ∧ ∃ s', RatChart.IsRatSheetAt J p q x s'
    · obtain ⟨W, hW, hxW, hWE⟩ := hL n d J A p q f φ x hf hφ hx.1 hx.2
      exact ⟨W, hW, fun _ _ => hxW, fun E hE hEW => (hWE E hE hEW).symm⟩
    · refine ⟨∅, isOpen_empty, fun h1 h2 => absurd ⟨h1, h2⟩ hx, fun E _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.indicator_empty]
      simp [chartPosDens, sheetSum, RatChart.ratPosDens, RatChart.ratSheetSum]
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
  have hcov : ∀ x ∈ zeroSet J, (∃ s, IsSheetAt J A x s) → (∃ s', RatChart.IsRatSheetAt J p q x s') →
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

  have haeR : ∀ᵐ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y) =
      ∑' k, ENNReal.ofReal (RatChart.ratPosDens J p q ((E k).indicator f) φ y) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hN1 n d J A p q hJ hd hA hfin)] with y hy
    refine ratPosDens_split f φ E y (hfin y) hEd fun x hx hs => hcov x hx.1 ?_ hs
    by_contra hn
    exact hy ⟨x, ⟨hx.1, hs, hn⟩, hx.2.2⟩
  have haeA : ∀ᵐ y, ENNReal.ofReal (chartPosDens J A f φ y) =
      ∑' k, ENNReal.ofReal (chartPosDens J A ((E k).indicator f) φ y) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hN2 n d J A p q hJ hd hA hq hfin)] with y hy
    refine PosPartSplit.proof n d J A f φ E y hA hEd fun x hx hs => hcov x hx.1 hs ?_
    by_contra hn
    exact hy ⟨x, ⟨hx.1, hs, hn⟩, hx.2⟩
  rw [lintegral_congr_ae haeR, lintegral_congr_ae haeA,
    lintegral_tsum fun k => (measurable_ratPosDens hM hfin (hf.indicator (hEm k)) φ).ennreal_ofReal.aemeasurable,
    lintegral_tsum fun k =>
      (IntegralIndep.measurable_chartPosDens hA (hf.indicator (hEm k)) φ).ennreal_ofReal.aemeasurable]
  exact tsum_congr fun k => hWE (e k) (E k) (hEm k) (hEW k)
end GroundTheory.Heights₂.Heights.RatChartChangeVar
