-- Prove2me | solution 1 for OAI.YauCounterexamples.three_annular_projection_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:33:11.07725+00:00
-- url     : https://prove2.me/submissions/c9c98ab4-73b1-4318-bf92-6337793faaa7

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_threeCoupled_conjugate_projection_uniform
import Theorems.Thm_OAI_YauCounterexamples_three_wave_exterior_germ

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma three_chart_symm_continuous (p : ThreeManifold) : Continuous (chartAt ThreeModel p).symm := by
  exact continuousOn_univ.mp (by simpa only [OpenPartialHomeomorph.symm_source,three_chart_target] using
    (chartAt ThreeModel p).symm.continuousOn)
end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ChartGradientProjectionCongrNhds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
section ProjectionGerm
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma chartGradientProjection_congr_nhds (g : SmoothMetric E M) (p : M)
    {u v : M → ℝ} {y : E} (hy : y ∈ (chartAt E p).target)
    (he : u =ᶠ[𝓝 ((chartAt E p).symm y)] v) (i j : CoordIndex E) :
    chartGradientProjection g u p i j =ᶠ[𝓝 y] chartGradientProjection g v p i j := by
  have hec := he.comp_tendsto ((chartAt E p).continuousAt_symm hy).tendsto
  have hdf := hec.fderiv (𝕜 := ℝ)
  filter_upwards [hdf] with z hz
  unfold chartGradientProjection chartGradientField coordinateFlux localGradientPair
  rw [show fderiv ℝ (u ∘ (chartAt E p).symm) z = fderiv ℝ (v ∘ (chartAt E p).symm) z from hz]
end ProjectionGerm

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ExistsThreeScalarProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma threeNormalInv_continuous : Continuous threeNormalInv :=
  (continuousOn_univ.mp (by simpa only [three_chart_target] using (chartAt ThreeModel threeProfileCenter).continuousOn_symm)).comp threeNormalEquiv.continuous
end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeCutoffControlBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma threeNormalInv_isOpenMap : IsOpenMap threeNormalInv := by
  intro U hU
  change IsOpen (((chartAt ThreeModel threeProfileCenter).symm ∘ threeNormalEquiv) '' U)
  rw [image_comp]
  exact (chartAt ThreeModel threeProfileCenter).isOpen_image_symm_of_subset_target
    (threeNormalEquiv.toHomeomorph.isOpenMap U hU) (by rw [three_chart_target]; exact subset_univ _)
lemma threeNormalInv_closedBall_closed (r : ℝ) : IsClosed (threeNormalInv '' closedBall 0 r) :=
  ((isCompact_closedBall (0:NormalWaveSpace) r).image threeNormalInv_continuous).isClosed
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma threeAnnulus_closed (d e : ℝ) : IsClosed (ThreeAnnulus d e) :=
  (threeNormalInv_closedBall_closed e).sdiff (threeNormalInv_isOpenMap _ isOpen_ball)
lemma threeAnnulus_not_inner {c d e : ℝ} (hcd : c<d) {q : ThreeManifold}
    (hq : q∈ThreeAnnulus d e) : q∉threeNormalInv '' closedBall 0 c := by
  intro h
  apply hq.2
  exact image_mono (closedBall_subset_ball hcd) h
lemma threeAnnulus_clean {d e R : ℝ} (heR : e≤R) (hc : ThreeCleanBall R)
    {q : ThreeManifold} (hq : q∈ThreeAnnulus d e) :
    1/2≤‖productA q.1‖ ∧ ‖productA q.1‖≤3/4 := by
  obtain ⟨y,hy,rfl⟩ := hq.1
  exact hc y (closedBall_subset_closedBall heR hy)
theorem three_annular_projection_uniform_oai
    (g : SmoothMetric ThreeModel ThreeManifold)
    {F : Set ThreeManifold} {c d e R : ℝ} (hcd : c<d) (heR : e≤R)
    (hclean : ThreeCleanBall R) (hFc : F⊆threeNormalInv '' closedBall 0 c)
    (hext : ∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
      g.inner q v w=threeBackgroundMetric.inner q v w)
    (tests : List (CoordinateTest ThreeModel ThreeManifold)) (h : ℕ) {D : ℝ} (hD : 0≤D) :
    ∃ C>0, ∀ w : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ w →
      (∀ q, 1/2≤w q) → (∀ q, w q≤2) →
      (∀ t∈tests, ∀ y∈t.compactSet, ∀ j≤h+1,
        ‖iteratedFDeriv ℝ j (w ∘ (chartAt ThreeModel t.center).symm) y‖≤D) →
      (∀ q, coordinateGradientPair g w w q≤1/4096) →
      ∀ {u : NormalWaveSpace → ℝ}, HasCompactSupport u → tsupport u⊆closedBall 0 c →
      ∀ n : ℕ, 1≤n → ∀ t∈tests, ∀ y∈t.compactSet,
      (chartAt ThreeModel t.center).symm y∈ThreeAnnulus d e →
      ∀ i j : CoordIndex ThreeModel, ∀ k≤h,
        ‖iteratedFDeriv ℝ k (chartGradientProjection g
          (fun q => (threeCoupled threeCouplingRadius n+threeWaveLift u) q/w q)
          t.center i j) y‖≤C*(n:ℝ)^k := by
  classical
  let K (t : CoordinateTest ThreeModel ThreeManifold) := t.compactSet ∩
    (chartAt ThreeModel t.center).symm ⁻¹' ThreeAnnulus d e
  have hKt (t : CoordinateTest ThreeModel ThreeManifold) : IsCompact (K t) :=
    t.isCompact.inter_right ((threeAnnulus_closed d e).preimage (three_chart_symm_continuous t.center))
  have hKO (t : CoordinateTest ThreeModel ThreeManifold) : K t⊆(chartAt ThreeModel t.center).target :=
    fun y hy => t.inTarget hy.1
  have hg (t : CoordinateTest ThreeModel ThreeManifold) (y : ThreeModel) (hy : y∈K t)
      (v z : TangentSpace 𝓘(ℝ,ThreeModel) ((chartAt ThreeModel t.center).symm y)) :
      g.inner _ v z=threeBackgroundMetric.inner _ v z :=
    hext _ (fun hf => threeAnnulus_not_inner hcd hy.2 (hFc hf)) v z
  choose C hC hCJ using fun (t : CoordinateTest ThreeModel ThreeManifold) (k : Fin (h+1)) =>
    threeCoupled_conjugate_projection_uniform g t.center (hKt t) (hKO t) (hg t) k.val hD
      (fun y hy => (threeAnnulus_clean heR hclean hy.2).1)
      (fun y hy => (threeAnnulus_clean heR hclean hy.2).2)
  let B := 1+∑ t∈tests.toFinset, ∑ k : Fin (h+1), C t k
  have hB : 0<B := by
    apply add_pos_of_pos_of_nonneg zero_lt_one
    exact Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun k _ => (hC t k).le))
  have hCB (t : CoordinateTest ThreeModel ThreeManifold) (ht : t∈tests) (k : Fin (h+1)) : C t k≤B := by
    have hk := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset (Fin (h+1)))) => (hC t k).le)
      (Finset.mem_univ k)
    have ht' := Finset.single_le_sum (fun t (_ : t∈tests.toFinset) =>
      Finset.sum_nonneg (fun k (_ : k∈(Finset.univ : Finset (Fin (h+1)))) => (hC t k).le))
      (List.mem_toFinset.mpr ht)
    change C t k≤1+_
    linarith
  refine ⟨B,hB,?_⟩
  intro w hw hwl hwu hwJ hwG u hc hs n hn t ht y hy hann i j k hk
  let k' : Fin (h+1) := ⟨k,by omega⟩
  have hK : y∈K t := ⟨hy,hann⟩
  have hw0 : ∀ q, w q≠0 := fun q => ne_of_gt (by linarith [hwl q])
  have hp := hCJ t k' w hw hw0 (fun y _ => hwl _) (fun y _ => hwu _)
    (fun j _ hj y hy => hwJ t ht y hy.1 j (by have := k'.isLt; omega))
    (fun y _ => hwG _) n hn y hK i j
  have he := three_wave_exterior_germ hc hs n (threeAnnulus_not_inner hcd hann)
  have hew : (fun q => (threeCoupled threeCouplingRadius n+threeWaveLift u) q/w q) =ᶠ[𝓝 ((chartAt ThreeModel t.center).symm y)]
      (fun q => threeCoupled threeCouplingRadius n q/w q) := by
    filter_upwards [he] with q hq
    rw [hq]
  have heP := (chartGradientProjection_congr_nhds g t.center (t.inTarget hy) hew i j).iteratedFDeriv ℝ k
  rw [heP.eq_of_nhds]
  exact hp.trans (mul_le_mul_of_nonneg_right (hCB t ht k') (pow_nonneg (Nat.cast_nonneg n) k))
end


open Set Filter Function Manifold Metric BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.three_annular_projection_uniform_oai := @OAI.YauCounterexamples.three_annular_projection_uniform_oai
