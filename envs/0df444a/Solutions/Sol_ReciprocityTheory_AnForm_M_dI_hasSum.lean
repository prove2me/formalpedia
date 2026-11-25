-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.dI_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:16.192426+00:00
-- url     : https://prove2.me/submissions/86b0e1a9-dadf-4f72-80cb-42ece09ecf1e

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA
import Theorems.Thm_ReciprocityTheory_AnForm_M_dI_mset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) (G : X → ℝ)
    (hG : ∀ j, IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * G ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target)
    (E : ℕ → Set X) (hE : ∀ m, MeasurableSet (E m)) (hd : Pairwise (Function.onFun Disjoint E))
    (N : Set X) (hN : ∀ j, volume ((A.chart j) '' (N ∩ (A.chart j).source)) = 0)
    (hcov : (⋃ m, E m) = Nᶜ) :
    HasSum (fun m => integralWith A P Φ ((E m).indicator G)) (integralWith A P Φ G) := by
  unfold integralWith
  refine hasSum_sum (fun j _ => ?_)
  have hR : ∀ m, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' E m) :=
    fun m => dI_mset _ (hE m)
  have hRd : Pairwise (Function.onFun Disjoint
      fun m => (A.chart j).target ∩ (A.chart j).symm ⁻¹' E m) := by
    intro m m' hmm'
    exact ((hd hmm').preimage _).mono Set.inter_subset_right Set.inter_subset_right
  have hsub : (⋃ m, (A.chart j).target ∩ (A.chart j).symm ⁻¹' E m) ⊆ (A.chart j).target :=
    Set.iUnion_subset fun m => Set.inter_subset_left
  have H := hasSum_integral_iUnion hR hRd ((hG j).mono_set hsub)
  have h1 : ∀ m, ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) *
      (E m).indicator G ((A.chart j).symm y) * locDens A Φ j y =
      ∫ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' E m, P.χ j ((A.chart j).symm y) *
        G ((A.chart j).symm y) * locDens A Φ j y := by
    intro m
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (A.chart j).open_target.measurableSet
      Set.inter_subset_left ?_]
    · refine setIntegral_congr_fun (hR m) (fun y hy => ?_)
      rw [Set.indicator_of_mem (show (A.chart j).symm y ∈ E m from hy.2)]
    · rintro y ⟨hy, hyR⟩
      have : (A.chart j).symm y ∉ E m := fun h => hyR ⟨hy, h⟩
      simp [Set.indicator_of_notMem this]
  have h2 : ∫ y in (A.chart j).target, P.χ j ((A.chart j).symm y) * G ((A.chart j).symm y) *
      locDens A Φ j y = ∫ y in ⋃ m, (A.chart j).target ∩ (A.chart j).symm ⁻¹' E m,
        P.χ j ((A.chart j).symm y) * G ((A.chart j).symm y) * locDens A Φ j y := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      (A.chart j).open_target.measurableSet.nullMeasurableSet hsub ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hN j)] with y hy hyd
    exfalso
    apply hy
    have hyt := hyd.1
    have hnot : (A.chart j).symm y ∉ ⋃ m, E m := fun h => by
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 h
      exact hyd.2 (Set.mem_iUnion.2 ⟨m, hyt, hm⟩)
    rw [hcov, Set.mem_compl_iff, not_not] at hnot
    exact ⟨_, ⟨hnot, (A.chart j).map_target hyt⟩, (A.chart j).right_inv hyt⟩
  simp only [h1, h2]
  exact H
end ReciprocityTheory.AnForm.M
