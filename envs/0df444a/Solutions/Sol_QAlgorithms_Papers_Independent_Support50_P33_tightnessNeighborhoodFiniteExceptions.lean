-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P33.tightnessNeighborhoodFiniteExceptions
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:48:28.399587+00:00
-- url     : https://prove2.me/submissions/80a5afa4-450b-4fbc-afa2-42641dfb8151

import Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P33_tightnessNeighborhoodCriterion

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace X9FiniteExceptions

lemma secondCountable_of_inducing_separable {X E : Type*} [MetricSpace X] [UniformSpace E]
    (f : X → E) (hf : IsUniformInducing f) (hs : IsSeparable (range f)) :
    SecondCountableTopology X := by
  classical
  apply UniformSpace.secondCountable_of_almost_dense_set
  intro U hU
  rw [← hf.comap_uniformity, mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  obtain ⟨W, hW, hWs, hWW⟩ := comp_symm_of_uniformity hV
  obtain ⟨C, hC, hclosure⟩ := hs
  let D := {c : E | c ∈ C ∧ ∃ x : X, (c, f x) ∈ W}
  have hD : D.Countable := hC.mono fun _ h => h.1
  let g : D → X := fun c => Classical.choose c.2.2
  have hg (c : D) : (c.val, f (g c)) ∈ W := Classical.choose_spec c.2.2
  letI := hD.to_subtype
  refine ⟨range g, countable_range g, eq_univ_iff_forall.mpr fun x => ?_⟩
  obtain ⟨c, hxc, hc⟩ := UniformSpace.mem_closure_iff_ball.mp (hclosure (mem_range_self x)) hW
  have hcx : (c, f x) ∈ W := hWs hxc
  let c' : D := ⟨c, hc, x, hcx⟩
  refine mem_iUnion₂.mpr ⟨g c', mem_range_self c', ?_⟩
  apply hVU
  exact hWW ⟨c, hWs (hg c'), hcx⟩


lemma tight_finite {X : Type*} [MetricSpace X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (F : Set (ProbabilityMeasure X)) (hF : F.Finite) :
    IsTightMeasureSet ((fun mu : ProbabilityMeasure X => (mu : Measure X)) '' F) := by
  induction F, hF using Set.Finite.induction_on with
  | empty =>
      apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
      intro e he
      exact ⟨∅, isCompact_empty, by simp⟩
  | @insert mu F hmu hF ih =>
      rw [image_insert_eq]
      exact isTightMeasureSet_singleton.union ih

end X9FiniteExceptions

open QAlgorithms.Papers.Independent.Support50.P33
open QAlgorithms.Papers.Independent.Frontier18.P10
attribute [local instance] QAlgorithms.Papers.Independent.Support50.P33.paperMeasurable
attribute [local instance] QAlgorithms.Papers.Independent.Support50.P33.paperBorel

theorem solution {E : Type*} [UniformSpace E] [AddCommGroup E] [Module ℝ E]
    [hgroup : IsUniformAddGroup E] [hsmul : ContinuousSMul ℝ E]
    [hlc : LocallyConvexSpace ℝ E] [hhaus : T2Space E]
    (A : Set E) (hA : GeneralBarycenterSpace A) (hc : Convex ℝ A)
    (d : MetricSpace A) (hd : d.toUniformSpace = (inferInstance : UniformSpace A))
    (M : Set (ProbabilityMeasure A)) :
    IsTightMeasureSet ((fun mu : ProbabilityMeasure A => (mu : Measure A)) '' M) ↔
      ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta →
        ∃ K : Set A, IsCompact K ∧
          ∃ F : Set (ProbabilityMeasure A), F ⊆ M ∧ F.Finite ∧
            ∀ mu ∈ M \ F, ENNReal.ofReal (1 - epsilon) ≤
              (mu : Measure A) (letI : MetricSpace A := d; Metric.cthickening delta K) := by
  classical
  have hclosed : closedConvexHull ℝ A = A := by
    rw [closedConvexHull_eq_closure_convexHull, hc.convexHull_eq, hA.1.closure_eq]
  have hcomplete : IsComplete A := by rw [← hclosed]; exact hA.2.2.1
  have hsep : IsSeparable A := by rw [← hclosed]; exact hA.2.2.2.1
  letI : CompleteSpace A := hcomplete.completeSpace_coe
  letI : MetricSpace A := d.replaceUniformity (congrArg (fun u : UniformSpace A => @uniformity A u) hd.symm)
  letI : SecondCountableTopology A := X9FiniteExceptions.secondCountable_of_inducing_separable
    (Subtype.val : A → E) isUniformEmbedding_subtype_val.isUniformInducing
    (by simpa only [Subtype.range_coe] using hsep)
  constructor
  · intro h e he r hr
    obtain ⟨K, hK, hb⟩ := (tightnessNeighborhoodCriterion A hA hc d hd M).mp h e he r hr
    exact ⟨K, hK, ∅, empty_subset M, finite_empty, fun mu hmu => hb mu hmu.1⟩
  · intro h
    apply (tightnessNeighborhoodCriterion A hA hc d hd M).mpr
    intro e he r hr
    obtain ⟨K, hK, F, hFM, hF, hb⟩ := h e he r hr
    obtain ⟨L, hL, hLmu⟩ := (tightnessNeighborhoodCriterion A hA hc d hd F).mp
      (X9FiniteExceptions.tight_finite F hF) e he r hr
    refine ⟨K ∪ L, hK.union hL, fun mu hmu => ?_⟩
    change ENNReal.ofReal (1-e) ≤ (mu : Measure A) (Metric.cthickening r (K ∪ L))
    change ∀ mu ∈ F, ENNReal.ofReal (1-e) ≤ (mu : Measure A) (Metric.cthickening r L) at hLmu
    change ∀ mu ∈ M \ F, ENNReal.ofReal (1-e) ≤ (mu : Measure A) (Metric.cthickening r K) at hb
    by_cases hmuF : mu ∈ F
    · exact (hLmu mu hmuF).trans (measure_mono (Metric.cthickening_subset_of_subset r subset_union_right))
    · exact (hb mu ⟨hmu, hmuF⟩).trans (measure_mono (Metric.cthickening_subset_of_subset r subset_union_left))
