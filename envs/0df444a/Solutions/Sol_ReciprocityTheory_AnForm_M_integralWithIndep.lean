-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.integralWithIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:30:19.741423+00:00
-- url     : https://prove2.me/submissions/8d6172da-4834-4574-ab4e-c3d96486c261

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntLocalize
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntegrableMul
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
end helpers
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : IntegralWithIndepStatement := by
  intro e X _ _ _ A P Q Φ hΦ g hg
  have hPg : ∀ j, MIntegrable A Φ (fun x => P.χ j x * g x) := fun j =>
    mIntegrableMul A Φ g (P.χ j) hg (smooth_continuous A (P.smooth j))
  have h1 : ∀ j, (∫ y in (A.chart j).target,
      P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y) =
      integralWith A Q Φ (fun x => P.χ j x * g x) := fun j =>
    (mIntLocalize A Q Φ hΦ j _ (tsupport_mul_subset_left.trans (P.tsupport_subset j)) (hPg j)).symm
  have hint : ∀ i j, IntegrableOn (fun y => Q.χ i ((A.chart i).symm y) *
      (P.χ j ((A.chart i).symm y) * g ((A.chart i).symm y)) * locDens A Φ i y)
      (A.chart i).target := fun i j =>
    integrableOn_target_of_tsupport A Φ i (fun x => Q.χ i x * (P.χ j x * g x))
      (tsupport_mul_subset_left.trans (Q.tsupport_subset i))
      (mIntegrableMul A Φ _ (Q.χ i) (hPg j) (smooth_continuous A (Q.smooth i)))
  calc integralWith A P Φ g = ∑ j, integralWith A Q Φ (fun x => P.χ j x * g x) :=
        Finset.sum_congr rfl (fun j _ => h1 j)
    _ = ∑ i, ∫ y in (A.chart i).target, ∑ j, Q.χ i ((A.chart i).symm y) *
          (P.χ j ((A.chart i).symm y) * g ((A.chart i).symm y)) * locDens A Φ i y := by
        unfold integralWith
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_finset_sum _ (fun j _ => hint i j)]
    _ = integralWith A Q Φ g := by
        unfold integralWith
        refine Finset.sum_congr rfl (fun i _ =>
          setIntegral_congr_fun (A.chart i).open_target.measurableSet (fun y _ => ?_))
        rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul, P.sum_eq_one, one_mul]
end ReciprocityTheory.AnForm.M
