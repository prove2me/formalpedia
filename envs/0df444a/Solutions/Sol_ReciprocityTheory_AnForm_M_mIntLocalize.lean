-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.mIntLocalize
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:02:15.646798+00:00
-- url     : https://prove2.me/submissions/ded8121f-21fd-4fd4-b590-28b9e6a0cdc3

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_jacC
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_image_eq_integral_normSq_det_smul
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
section helpers
variable {e : ℕ} {X : Type} [TopologicalSpace X]
private theorem smooth_continuous (A : FinHolAtlas e X) {f : X → ℝ} (hf : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) := by
    refine (hf j).continuousOn.continuousAt ?_
    rw [Set.preimage_univ, Set.inter_univ]
    exact (A.chart j).open_target.mem_nhds ((A.chart j).map_source hj)
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x :=
    h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with x' hx'
  simp [(A.chart j).left_inv hx']
private theorem integrableOn_target_of_tsupport [CompactSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (j : Fin A.n) (g : X → ℝ) (hs : tsupport g ⊆ (A.chart j).source)
    (hg : MIntegrable A Φ g) :
    IntegrableOn (fun y => g ((A.chart j).symm y) * locDens A Φ j y) (A.chart j).target := by
  have hK : IsCompact ((A.chart j) '' tsupport g) :=
    (isClosed_tsupport g).isCompact.image_of_continuousOn ((A.chart j).continuousOn.mono hs)
  have hKt : (A.chart j) '' tsupport g ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (hs hx)
  refine (hg j _ hKt hK).of_forall_diff_eq_zero (A.chart j).open_target.measurableSet ?_
  rintro y ⟨hy, hyK⟩
  have h0 : g ((A.chart j).symm y) = 0 := by
    by_contra h0
    exact hyK ⟨_, subset_tsupport _ (Function.mem_support.2 h0), (A.chart j).right_inv hy⟩
  simp [h0]
private theorem chart_move [CompactSpace X] (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (j k : Fin A.n) (g : X → ℝ)
    (hs : tsupport g ⊆ (A.chart j).source) :
    ∫ y in (A.chart k).target,
        P.χ k ((A.chart k).symm y) * g ((A.chart k).symm y) * locDens A Φ k y =
      ∫ y in (A.chart j).target,
        P.χ k ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y := by
  have hU : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart k).open_source
  have hinj : Set.InjOn (A.chart k ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) := by
    intro y hy y' hy' h
    have h1 : (A.chart j).symm y = (A.chart j).symm y' := (A.chart k).injOn hy.2 hy'.2 h
    rw [← (A.chart j).right_inv hy.1, ← (A.chart j).right_inv hy'.1, h1]
  have hsub : (A.chart k ∘ (A.chart j).symm) ''
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) ⊆ (A.chart k).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.chart k).map_source hy.2
  have e1 := setIntegral_eq_of_subset_of_forall_diff_eq_zero (μ := volume)
    (f := fun y => P.χ k ((A.chart k).symm y) * g ((A.chart k).symm y) * locDens A Φ k y)
    (A.chart k).open_target.measurableSet hsub (by
      rintro w ⟨hw, hnot⟩
      have hns : (A.chart k).symm w ∉ (A.chart j).source := by
        intro hsrc
        apply hnot
        refine ⟨A.chart j ((A.chart k).symm w), ⟨(A.chart j).map_source hsrc, ?_⟩, ?_⟩
        · simp only [Set.mem_preimage, (A.chart j).left_inv hsrc]
          exact (A.chart k).map_target hw
        · simp only [Function.comp_apply, (A.chart j).left_inv hsrc, (A.chart k).right_inv hw]
      have hg0 : g ((A.chart k).symm w) = 0 := by
        by_contra h0
        exact hns (hs (subset_tsupport _ (Function.mem_support.2 h0)))
      simp [hg0])
  have e2 := setIntegral_eq_of_subset_of_forall_diff_eq_zero (μ := volume)
    (f := fun y => P.χ k ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y)
    (A.chart j).open_target.measurableSet Set.inter_subset_left (by
      rintro y ⟨hy, hnot⟩
      have hns : (A.chart j).symm y ∉ (A.chart k).source := fun h => hnot ⟨hy, h⟩
      have hχ : P.χ k ((A.chart j).symm y) = 0 := by
        by_contra h0
        exact hns (P.tsupport_subset k (subset_tsupport _ (Function.mem_support.2 h0)))
      simp [hχ])
  rw [e1, e2, ReciprocityTheory.AnForm.A.integral_image_eq_integral_normSq_det_smul _ _ hU (A.holo j k) hinj]
  refine setIntegral_congr_fun hU.measurableSet (fun y hy => ?_)
  have hx := (A.chart k).left_inv hy.2
  simp only [Function.comp_apply, hx, smul_eq_mul]
  rw [locDensChart A Φ hΦ j k y hy.1 hy.2, ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq]
  ring
end helpers
private theorem mIntegrable_continuous_mul {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (g c : X → ℝ) (hg : MIntegrable A Φ g) (hc : Continuous c) :
    MIntegrable A Φ (fun x => c x * g x) := by
  intro j K hKt hK
  have hcK : ContinuousOn (fun y => c ((A.chart j).symm y)) K :=
    (hc.comp_continuousOn (A.chart j).continuousOn_symm).mono hKt
  simpa only [mul_assoc] using IntegrableOn.continuousOn_mul hcK (hg j K hKt hK) hK
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : MIntLocalizeStatement := by
  intro e X _ _ _ A P Φ hΦ j g hs hg
  have hint : ∀ k, IntegrableOn (fun y => P.χ k ((A.chart j).symm y) * g ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target := fun k =>
    integrableOn_target_of_tsupport A Φ j (fun x => P.χ k x * g x)
      (tsupport_mul_subset_right.trans hs)
      (mIntegrable_continuous_mul A Φ g (P.χ k) hg (smooth_continuous A (P.smooth k)))
  unfold integralWith
  rw [Finset.sum_congr rfl (fun k _ => chart_move A P Φ hΦ j k g hs),
    ← integral_finset_sum _ (fun k _ => hint k)]
  refine setIntegral_congr_fun (A.chart j).open_target.measurableSet (fun y _ => ?_)
  rw [← Finset.sum_mul, ← Finset.sum_mul, P.sum_eq_one, one_mul]
end ReciprocityTheory.AnForm.M
