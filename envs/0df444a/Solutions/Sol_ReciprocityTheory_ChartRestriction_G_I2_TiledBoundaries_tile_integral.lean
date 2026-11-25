-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.tile_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:26:29.086658+00:00
-- url     : https://prove2.me/submissions/9259a644-d87e-453b-84cb-aece80668e9f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_mem_reps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fd_uniq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fd_exists
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_tile_fund
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_bdd_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open MeasureTheory Module Set Submodule
noncomputable section
section Tile
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι]
variable (μ : Measure V) [μ.IsAddHaarMeasure]
private theorem isAddFundamentalDomain_zspan_fundamentalDomain (b : Basis ι ℝ V) (μ : Measure V) :
    IsAddFundamentalDomain (span ℤ (range b)).toAddSubgroup (ZSpan.fundamentalDomain b) μ := by
  refine IsAddFundamentalDomain.mk' (ZSpan.fundamentalDomain_measurableSet b).nullMeasurableSet ?_
  intro x
  obtain ⟨β, hβ, hβx⟩ := fd_exists b x
  refine ⟨⟨β, hβ⟩, hβx, ?_⟩
  rintro ⟨g, hg⟩ hgx
  exact Subtype.ext (fd_uniq b hg hβ hgx hβx)
private theorem setIntegral_preimage_sub_of_periodic (h : V → ℝ) (s : Set V) (c : V)
    (hper : ∀ x, h (x + c) = h x) :
    ∫ x in (fun x => x - c) ⁻¹' s, h x ∂μ = ∫ x in s, h x ∂μ := by
  have hf : (fun x : V => x - c) = fun x => -c + x := funext fun x => sub_eq_neg_add x c
  rw [hf]
  have hmp : MeasurePreserving (fun x : V => -c + x) μ μ := measurePreserving_add_left μ (-c)
  have he : MeasurableEmbedding (fun x : V => -c + x) := measurableEmbedding_addLeft (-c)
  calc ∫ x in (fun x => -c + x) ⁻¹' s, h x ∂μ
      = ∫ x in (fun x => -c + x) ⁻¹' s, h ((-c + x) + c) ∂μ := by
        congr 1; ext x; congr 1; abel
    _ = ∫ y in s, h (y + c) ∂μ := hmp.setIntegral_preimage_emb he (fun y => h (y + c)) s
    _ = ∫ y in s, h y ∂μ := by simp only [hper]
private theorem setIntegral_finset_biUnion_of_pairwise_disjoint (h : V → ℝ) (s : V → Set V) :
    ∀ t : Finset V, (∀ i ∈ t, MeasurableSet (s i)) → Set.Pairwise ↑t (Function.onFun Disjoint s) →
      (∀ i ∈ t, IntegrableOn h (s i) μ) →
      ∫ x in ⋃ i ∈ t, s i, h x ∂μ = ∑ i ∈ t, ∫ x in s i, h x ∂μ := by
  classical
  intro t
  refine Finset.induction_on t ?_ ?_
  · intro _ _ _
    simp
  · intro a t ha ih hs hd hf
    have hs' : ∀ i ∈ t, MeasurableSet (s i) := fun i hi => hs i (Finset.mem_insert_of_mem hi)
    have hf' : ∀ i ∈ t, IntegrableOn h (s i) μ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hd' : Set.Pairwise ↑t (Function.onFun Disjoint s) :=
      hd.mono (Finset.coe_subset.2 (Finset.subset_insert a t))
    have hdisj : Disjoint (s a) (⋃ i ∈ t, s i) := by
      refine Set.disjoint_iUnion₂_right.2 fun i hi => ?_
      have hne : a ≠ i := fun e => ha (e ▸ hi)
      exact hd (Finset.mem_coe.2 (Finset.mem_insert_self a t))
        (Finset.mem_coe.2 (Finset.mem_insert_of_mem hi)) hne
    have hint_r : IntegrableOn h (⋃ i ∈ t, s i) μ := integrableOn_finset_iUnion.2 hf'
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha,
      setIntegral_union hdisj (Finset.measurableSet_biUnion t hs') (hf a (Finset.mem_insert_self a t))
        hint_r, ih hs' hd' hf']
end Tile
end
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open MeasureTheory Module Set Submodule
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι]
variable (μ : Measure V) [μ.IsAddHaarMeasure]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (bA bB : Basis ι ℝ V) (hAB : span ℤ (range bA) ≤ span ℤ (range bB))
    (h : V → ℝ) (hc : Continuous h)
    (hper : ∀ β ∈ span ℤ (range bB), ∀ x, h (x + β) = h x) :
    ∫ x in ZSpan.fundamentalDomain bA, h x ∂μ =
      (reps bA bB).card * ∫ x in ZSpan.fundamentalDomain bB, h x ∂μ := by
  have : VAddInvariantMeasure (span ℤ (range bA)).toAddSubgroup V μ :=
    ⟨fun g s _ => measure_preimage_add μ (g : V) s⟩
  have hA := isAddFundamentalDomain_zspan_fundamentalDomain bA μ
  have hT := tile_fund bA bB hAB μ
  have hperA : ∀ (g : (span ℤ (range bA)).toAddSubgroup) (x : V), h (g +ᵥ x) = h x := by
    intro g x
    have hg : (g : V) ∈ span ℤ (range bA) := g.2
    change h ((g : V) + x) = h x
    rw [add_comm]
    exact hper _ (hAB hg) x
  rw [hA.setIntegral_eq hT hperA]
  unfold tileT
  rw [setIntegral_finset_biUnion_of_pairwise_disjoint μ h (fun c => (fun x => x - c) ⁻¹' ZSpan.fundamentalDomain bB)
    (reps bA bB) ?_ ?_ ?_]
  · rw [Finset.sum_congr rfl (g := fun _ => ∫ x in ZSpan.fundamentalDomain bB, h x ∂μ) fun c hc =>
      setIntegral_preimage_sub_of_periodic μ h (ZSpan.fundamentalDomain bB) c (hper c (mem_reps.1 hc).2),
      Finset.sum_const, nsmul_eq_mul]
  · intro c _
    exact (ZSpan.fundamentalDomain_measurableSet bB).preimage (continuous_sub_right c).measurable
  · intro c1 hc1 c2 hc2 hne
    refine Set.disjoint_left.2 fun x hx1 hx2 => hne ?_
    have e := fd_uniq bB
      (neg_mem (mem_reps.1 (Finset.mem_coe.1 hc1)).2)
      (neg_mem (mem_reps.1 (Finset.mem_coe.1 hc2)).2) (x := x)
      (by rw [neg_add_eq_sub]; exact hx1) (by rw [neg_add_eq_sub]; exact hx2)
    exact neg_inj.1 e
  · intro c _
    have hb := bdd_trans (ZSpan.fundamentalDomain_isBounded bB) c
    have hK : IsCompact (closure ((fun x => x - c) ⁻¹' ZSpan.fundamentalDomain bB)) := by
      first
        | exact hb.isCompact_closure
        | exact Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
    first
      | exact ((hc.locallyIntegrable (μ := μ)).integrableOn_isCompact hK).mono_set subset_closure
      | exact (hc.continuousOn.integrableOn_compact hK).mono_set subset_closure
      | exact (hc.integrableOn_isCompact hK).mono_set subset_closure
      | exact (hc.continuousOn.integrableOn_isCompact hK).mono_set subset_closure
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
