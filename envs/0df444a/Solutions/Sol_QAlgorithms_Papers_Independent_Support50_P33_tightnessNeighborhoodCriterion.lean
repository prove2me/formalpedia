-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P33.tightnessNeighborhoodCriterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:44:33.058308+00:00
-- url     : https://prove2.me/submissions/cab5a2ab-8888-4b09-9f9f-77428beb59e2

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P33

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace X9Tightness

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma lower_iff_compl (mu : ProbabilityMeasure X) {s : Set X}
    (hs : MeasurableSet s) (e : ℝ) (he : 0 ≤ e) :
    ENNReal.ofReal (1-e) ≤ (mu : Measure X) s ↔
      (mu : Measure X) sᶜ ≤ ENNReal.ofReal e := by
  rw [measure_compl hs (measure_ne_top _ _), measure_univ,
    ENNReal.ofReal_sub 1 he, ENNReal.ofReal_one]
  exact tsub_le_iff_tsub_le

lemma compact_inter [CompleteSpace X] (K : ℕ → Set X) (hK : ∀ n, IsCompact (K n))
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) (hr0 : Tendsto r atTop (𝓝 0)) :
    IsCompact (⋂ n, Metric.cthickening (r n) (K n)) := by
  apply TotallyBounded.isCompact_of_isClosed
  · apply Metric.totallyBounded_iff.mpr
    intro e he
    obtain ⟨n, hn⟩ := (hr0.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < e/2))).exists
    obtain ⟨T, hT, hcover⟩ := Metric.totallyBounded_iff.mp (hK n).totallyBounded (e/2) (by positivity)
    refine ⟨T, hT, ?_⟩
    intro x hx
    have hx' := mem_iInter.mp hx n
    rw [(hK n).cthickening_eq_biUnion_closedBall (hr n)] at hx'
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx'
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp (hcover hy)
    refine mem_iUnion₂.mpr ⟨z, hz, ?_⟩
    have := dist_triangle x y z
    simp only [Metric.mem_closedBall, Metric.mem_ball] at *
    linarith
  · exact isClosed_iInter fun _ => Metric.isClosed_cthickening


lemma neighborhood_criterion [CompleteSpace X] (M : Set (ProbabilityMeasure X)) :
    IsTightMeasureSet ((fun mu : ProbabilityMeasure X => (mu : Measure X)) '' M) ↔
      ∀ e : ℝ, 0 < e → ∀ r : ℝ, 0 < r →
        ∃ K : Set X, IsCompact K ∧ ∀ mu ∈ M,
          ENNReal.ofReal (1-e) ≤ (mu : Measure X) (Metric.cthickening r K) := by
  constructor
  · intro h e he r _
    obtain ⟨K, hK, hb⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp h
      (ENNReal.ofReal e) (ENNReal.ofReal_pos.mpr he)
    refine ⟨K, hK, fun mu hmu => ?_⟩
    apply (lower_iff_compl mu Metric.isClosed_cthickening.measurableSet e he.le).mpr
    exact (measure_mono (compl_subset_compl.mpr (Metric.self_subset_cthickening K))).trans
      (hb _ (mem_image_of_mem _ hmu))
  · intro h
    apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
    intro q hq
    by_cases hqt : q = ⊤
    · exact ⟨∅, isCompact_empty, by simp [hqt]⟩
    let e := q.toReal
    have he : 0 < e := ENNReal.toReal_pos hq.ne' hqt
    let r : ℕ → ℝ := fun n => (1/2)^n
    let u : ℕ → ℝ := fun n => e/2/2^n
    have hr : ∀ n, 0 < r n := fun n => by dsimp [r]; positivity
    have hu : ∀ n, 0 < u n := fun n => by dsimp [u]; positivity
    obtain ⟨K, hK, hb⟩ : ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧
        ∀ n, ∀ mu ∈ M, ENNReal.ofReal (1-u n) ≤
          (mu : Measure X) (Metric.cthickening (r n) (K n)) := by
      choose K hK hb using fun n => h (u n) (hu n) (r n) (hr n)
      exact ⟨K, hK, hb⟩
    let L := ⋂ n, Metric.cthickening (r n) (K n)
    have hL : IsCompact L := compact_inter K hK r (fun n => (hr n).le)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    refine ⟨L, hL, ?_⟩
    rintro _ ⟨mu, hmu, rfl⟩
    calc
      (mu : Measure X) Lᶜ = (mu : Measure X) (⋃ n, (Metric.cthickening (r n) (K n))ᶜ) := by
        simp only [L, compl_iInter]
      _ ≤ ∑' n, (mu : Measure X) (Metric.cthickening (r n) (K n))ᶜ := measure_iUnion_le _
      _ ≤ ∑' n, ENNReal.ofReal (u n) := ENNReal.tsum_le_tsum fun n =>
        (lower_iff_compl mu Metric.isClosed_cthickening.measurableSet (u n) (hu n).le).mp
          (hb n mu hmu)
      _ = ENNReal.ofReal (∑' n, u n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => (hu n).le) (summable_geometric_two' e)).symm
      _ = q := by rw [tsum_geometric_two' e]; exact ENNReal.ofReal_toReal hqt

end X9Tightness

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
          ∀ mu ∈ M, ENNReal.ofReal (1 - epsilon) ≤
            (mu : Measure A) (letI : MetricSpace A := d; Metric.cthickening delta K) := by
  have hclosed : closedConvexHull ℝ A = A := by
    rw [closedConvexHull_eq_closure_convexHull, hc.convexHull_eq, hA.1.closure_eq]
  have hcomplete : IsComplete A := by rw [← hclosed]; exact hA.2.2.1
  letI : CompleteSpace A := hcomplete.completeSpace_coe
  letI : MetricSpace A := d.replaceUniformity (congrArg (fun u : UniformSpace A => @uniformity A u) hd.symm)
  exact X9Tightness.neighborhood_criterion M
