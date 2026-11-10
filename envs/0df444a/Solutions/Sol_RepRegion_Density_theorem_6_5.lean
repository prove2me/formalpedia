-- Prove2me | solution 1 for RepRegion.Density.theorem_6_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T22:15:10.64704+00:00
-- url     : https://prove2.me/submissions/315d082a-ee17-419d-bd86-08077c4e75c7

import Mathlib
import Definitions.Def_RepRegion_Density_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology ENNReal

namespace RepRegionD087

/-- L0: a compact set is measurable when closed balls are (no Borel assumption needed). -/
theorem isCompact_measurableSet {M : Type*} [MetricSpace M] [MeasurableSpace M]
    (hball : ∀ (x : M) (r : ℝ), MeasurableSet (Metric.closedBall x r))
    {K : Set M} (hKc : IsCompact K) : MeasurableSet K := by
  have hk : ∀ k : ℕ, ∃ t ⊆ K, t.Finite ∧ K ⊆ ⋃ x ∈ t, Metric.ball x (1 / ((k : ℝ) + 1)) :=
    fun k => finite_cover_balls_of_compact hKc (by positivity)
  choose t htK htf htc using hk
  have hEq : K = ⋂ k : ℕ, ⋃ x ∈ t k, Metric.closedBall x (1 / ((k : ℝ) + 1)) := by
    apply Set.Subset.antisymm
    · intro y hy
      rw [Set.mem_iInter]
      intro k
      have := htc k hy
      rw [Set.mem_iUnion₂] at this ⊢
      obtain ⟨x, hx, hyx⟩ := this
      exact ⟨x, hx, Metric.ball_subset_closedBall hyx⟩
    · intro y hy
      rw [Set.mem_iInter] at hy
      rw [← hKc.isClosed.closure_eq, Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      have := hy k
      rw [Set.mem_iUnion₂] at this
      obtain ⟨x, hx, hyx⟩ := this
      refine ⟨x, htK k hx, ?_⟩
      rw [Metric.mem_closedBall] at hyx
      linarith
  rw [hEq]
  exact MeasurableSet.iInter fun k => (htf k).measurableSet_biUnion fun x _ => hball x _

/-- L4: uniform continuity of a continuous function near a compact set. -/
theorem unif_near {M : Type*} [MetricSpace M] {g : M → ℝ} (hgc : Continuous g)
    {K : Set M} (hKc : IsCompact K) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ s ∈ K, ∀ x, dist x s ≤ ρ → |g x - g s| ≤ η := by
  have hr : {p : ℝ × ℝ | dist p.1 p.2 < η} ∈ uniformity ℝ := Metric.dist_mem_uniformity hη
  have := hKc.uniformContinuousAt_of_continuousAt g (fun a _ => hgc.continuousAt) hr
  obtain ⟨ε, hε, hU⟩ := Metric.mem_uniformity_dist.1 this
  refine ⟨ε / 2, by positivity, fun s hs x hx => ?_⟩
  have h1 : dist s x < ε := by rw [dist_comm]; linarith
  have := hU h1 hs
  simp only [Set.mem_ofPred_eq, Real.dist_eq] at this
  rw [abs_sub_comm]
  exact this.le

/-- L1: almost surely every sample point lies in `K`. -/
theorem sample_mem_K {M Ω : Type*} [MetricSpace M] [MeasurableSpace M] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → M)
    (hXm : ∀ i, Measurable (X i)) (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    {K : Set M} (hKm : MeasurableSet K) (hK1 : P.map (X 0) K = 1) :
    ∀ᵐ ω ∂P, ∀ i, X i ω ∈ K := by
  rw [ae_all_iff]
  intro i
  have h1 : P.map (X i) K = 1 := by rw [(hid i).map_eq]; exact hK1
  rw [Measure.map_apply (hXm i) hKm] at h1
  rw [ae_iff]
  exact (prob_compl_eq_zero_iff (hXm i hKm)).2 h1

/-- L2: SLLN for the empirical frequency of one measurable set. -/
theorem slln_set {M Ω : Type*} [MeasurableSpace M] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → M)
    (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) {T : Set M} (hT : MeasurableSet T) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => RepRegion.Density.empFreq X n ω T) atTop
      (𝓝 ((P.map (X 0)) T).toReal) := by
  set Y : ℕ → Ω → ℝ := fun i ω => T.indicator (fun _ => (1 : ℝ)) (X i ω) with hY
  have hYm : ∀ i, Measurable (Y i) :=
    fun i => (measurable_const.indicator hT).comp (hXm i)
  have hint : Integrable (Y 0) P := by
    refine Integrable.of_bound (hYm 0).aestronglyMeasurable 1 (Eventually.of_forall fun ω => ?_)
    simp only [hY, Set.indicator]
    split_ifs <;> simp
  have hindep : Pairwise (Function.onFun (fun f g => IndepFun f g P) Y) := by
    intro i j hij
    exact hind.indepFun hij |>.comp (measurable_const.indicator hT) (measurable_const.indicator hT)
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P :=
    fun i => (hid i).comp (measurable_const.indicator hT)
  have hmean : P[Y 0] = ((P.map (X 0)) T).toReal := by
    rw [Measure.map_apply (hXm 0) hT]
    have : Y 0 = (X 0 ⁻¹' T).indicator (fun _ => (1 : ℝ)) := by
      funext ω; rfl
    rw [this, integral_indicator_const _ ((hXm 0) hT), smul_eq_mul, mul_one]
    rfl
  filter_upwards [strong_law_ae_real Y hint hindep hident] with ω hω
  rw [hmean] at hω
  refine hω.congr fun n => ?_
  simp only [RepRegion.Density.empFreq, hY]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Set.indicator]

/-- empirical frequency is monotone along sample inclusions. -/
theorem emp_mono {M Ω : Type*} (X : ℕ → Ω → M) (n : ℕ) (ω : Ω) {T₁ T₂ : Set M}
    (h : ∀ i < n, X i ω ∈ T₁ → X i ω ∈ T₂) :
    RepRegion.Density.empFreq X n ω T₁ ≤ RepRegion.Density.empFreq X n ω T₂ := by
  unfold RepRegion.Density.empFreq
  gcongr ?_ / _
  apply Nat.cast_le.2
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨hi.1, h i hi.1 hi.2⟩

/-- L3a: deterministic bracketing of one region by finite unions of closed balls. -/
theorem bracket {M Θ : Type*} [MetricSpace M] [MeasurableSpace M]
    (ν : Measure M) [IsFiniteMeasure ν]
    {K : Set M} (hKc : IsCompact K) (hK0 : ν Kᶜ = 0)
    (C : Set (Set M)) (R : Θ → ℝ → Set M)
    (hUS : RepRegion.Density.UniformScale C R) (hUC : RepRegion.Density.UnifContWrt C R ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Set M, t.Finite ∧ ∃ r : ℝ, ∀ A ∈ C, ∃ sI ⊆ t, ∃ sO ⊆ t,
      (⋃ x ∈ sI, Metric.closedBall x r) ⊆ A ∧ A ∩ K ⊆ (⋃ x ∈ sO, Metric.closedBall x r) ∧
      ν ((⋃ x ∈ sO, Metric.closedBall x r) \ A) ≤ ENNReal.ofReal ε ∧
      ν (A \ ⋃ x ∈ sI, Metric.closedBall x r) ≤ ENNReal.ofReal ε := by
  unfold RepRegion.Density.UniformScale RepRegion.Density.IsScalableClass at hUS
  unfold RepRegion.Density.UnifContWrt at hUC
  obtain ⟨⟨⟨Ξ, hΞ, hCeq⟩, hmono⟩, hUSε⟩ := hUS
  obtain ⟨-, hRm, hUCε⟩ := hUC
  obtain ⟨d1, hd1, hd1'⟩ := hUCε ε hε
  obtain ⟨d2, hd2, hd2'⟩ := hUSε d1 hd1
  obtain ⟨t, -, htf, htc⟩ := finite_cover_balls_of_compact hKc (half_pos hd2)
  refine ⟨t, htf, d2 / 2, fun A hA => ?_⟩
  have hA' := hA
  rw [hCeq] at hA'
  obtain ⟨⟨θ, l⟩, hp, hAeq⟩ := hA'
  have hAeq' : A = R θ l := hAeq
  subst hAeq'
  have hl : 0 < l := hΞ _ hp
  obtain ⟨hout, hin⟩ := hd2' θ l hl hA
  obtain ⟨hνout, hνin⟩ := hd1' θ l hl hA
  have hball2 : ∀ c y : M, dist y c ≤ d2 / 2 →
      Metric.closedBall c (d2 / 2) ⊆ Metric.closedBall y d2 := by
    intro c y hyc z hz
    rw [Metric.mem_closedBall] at hz ⊢
    linarith [dist_triangle z c y, dist_comm y c]
  have hEm : MeasurableSet (RepRegion.Density.regionExt R θ (l - d1)) := by
    unfold RepRegion.Density.regionExt
    split_ifs with h
    · exact hRm θ _ h
    · exact MeasurableSet.empty
  have hEsub : RepRegion.Density.regionExt R θ (l - d1) ⊆ R θ l := by
    unfold RepRegion.Density.regionExt
    split_ifs with h
    · exact hmono θ _ _ h (by linarith)
    · exact Set.empty_subset _
  have hsub1 : R θ l ⊆ R θ (l + d1) := hmono θ _ _ hl (by linarith)
  refine ⟨{c ∈ t | Metric.closedBall c (d2 / 2) ⊆ R θ l}, fun c hc => hc.1,
    {c ∈ t | ∃ z ∈ R θ l, z ∈ Metric.closedBall c (d2 / 2)}, fun c hc => hc.1, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.1 hy
    exact hc.2 hyc
  · rintro y ⟨hyA, hyK⟩
    obtain ⟨c, hct, hyc⟩ := Set.mem_iUnion₂.1 (htc hyK)
    exact Set.mem_iUnion₂.2 ⟨c, ⟨hct, y, hyA, Metric.ball_subset_closedBall hyc⟩,
      Metric.ball_subset_closedBall hyc⟩
  · have hOsub : (⋃ c ∈ {c ∈ t | ∃ z ∈ R θ l, z ∈ Metric.closedBall c (d2 / 2)},
        Metric.closedBall c (d2 / 2)) ⊆ R θ (l + d1) := by
      intro y hy
      obtain ⟨c, ⟨-, z, hz, hzc⟩, hyc⟩ := Set.mem_iUnion₂.1 hy
      exact hout z hz (hball2 c z (Metric.mem_closedBall.1 hzc) hyc)
    calc ν (_ \ R θ l) ≤ ν (R θ (l + d1) \ R θ l) := measure_mono (Set.diff_subset_diff_left hOsub)
      _ = ν (R θ (l + d1)) - ν (R θ l) :=
          measure_diff hsub1 (hRm θ l hl).nullMeasurableSet (measure_ne_top _ _)
      _ ≤ ENNReal.ofReal ε := by rw [tsub_le_iff_left]; exact hνout
  · have hsub : R θ l \ (⋃ c ∈ {c ∈ t | Metric.closedBall c (d2 / 2) ⊆ R θ l},
        Metric.closedBall c (d2 / 2)) ⊆
        (R θ l \ RepRegion.Density.regionExt R θ (l - d1)) ∪ Kᶜ := by
      rintro y ⟨hyA, hyI⟩
      by_contra hcon
      have hyE : y ∈ RepRegion.Density.regionExt R θ (l - d1) := by
        by_contra h; exact hcon (Or.inl ⟨hyA, h⟩)
      have hyK : y ∈ K := by
        by_contra h; exact hcon (Or.inr h)
      obtain ⟨c, hct, hyc⟩ := Set.mem_iUnion₂.1 (htc hyK)
      apply hyI
      refine Set.mem_iUnion₂.2 ⟨c, ⟨hct, ?_⟩, Metric.ball_subset_closedBall hyc⟩
      exact (hball2 c y (Metric.mem_ball.1 hyc).le).trans (hin y hyE)
    calc ν (R θ l \ _) ≤ ν ((R θ l \ RepRegion.Density.regionExt R θ (l - d1)) ∪ Kᶜ) :=
          measure_mono hsub
      _ ≤ ν (R θ l \ RepRegion.Density.regionExt R θ (l - d1)) + ν Kᶜ := measure_union_le _ _
      _ = ν (R θ l) - ν (RepRegion.Density.regionExt R θ (l - d1)) := by
          rw [hK0, add_zero, measure_diff hEsub hEm.nullMeasurableSet (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal ε := by rw [tsub_le_iff_left]; exact hνin

/-- L3: uniform (Glivenko-Cantelli) convergence over unions of at most `u` regions of `C`. -/
theorem gc_union {M Ω Θ : Type*} [MetricSpace M] [MeasurableSpace M] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → M)
    (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hball : ∀ (x : M) (r : ℝ), MeasurableSet (Metric.closedBall x r))
    {K : Set M} (hKc : IsCompact K) (hK1 : P.map (X 0) K = 1)
    (C : Set (Set M)) (R : Θ → ℝ → Set M)
    (hUS : RepRegion.Density.UniformScale C R)
    (hUC : RepRegion.Density.UnifContWrt C R (P.map (X 0))) :
    ∀ᵐ ω ∂P, ∀ η > 0, ∀ u : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ F : Finset (Set M), (↑F ⊆ C) →
      F.card ≤ u → |RepRegion.Density.empFreq X n ω (⋃ A ∈ F, A) -
        ((P.map (X 0)) (⋃ A ∈ F, A)).toReal| ≤ η := by
  haveI : IsProbabilityMeasure (P.map (X 0)) := Measure.isProbabilityMeasure_map (hXm 0).aemeasurable
  have hKm : MeasurableSet K := isCompact_measurableSet hball hKc
  have hK0 : (P.map (X 0)) Kᶜ = 0 := (prob_compl_eq_zero_iff hKm).2 hK1
  have hb := fun k : ℕ => bracket (P.map (X 0)) hKc hK0 C R hUS hUC
    (ε := 1 / ((k : ℝ) + 1)) (by positivity)
  choose t htf r hbr using hb
  obtain ⟨TT, hTT⟩ : ∃ TT : ℕ → Set (Set M),
      TT = fun k => (fun s => ⋃ x ∈ s, Metric.closedBall x (r k)) '' {s | s ⊆ t k} := ⟨_, rfl⟩
  have hTTf : ∀ k, (TT k).Finite := fun k => by
    rw [hTT]; exact ((htf k).finite_subsets).image _
  have hTTm : ∀ k, ∀ T ∈ TT k, MeasurableSet T := by
    intro k T hT
    rw [hTT] at hT
    obtain ⟨s, hs, rfl⟩ := hT
    exact ((htf k).subset hs).measurableSet_biUnion fun x _ => hball x _
  have hall : ∀ᵐ ω ∂P, ∀ k, ∀ T ∈ TT k, Tendsto (fun n : ℕ =>
      RepRegion.Density.empFreq X n ω T) atTop (𝓝 ((P.map (X 0)) T).toReal) :=
    ae_all_iff.2 fun k => (ae_ball_iff (hTTf k).countable).2 fun T hT =>
      slln_set P X hXm hind hid (hTTm k T hT)
  filter_upwards [hall, sample_mem_K P X hXm hid hKm hK1] with ω hω hωK
  intro η hη u
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((u : ℝ) + 1) / ((k : ℝ) + 1) < η / 2 := by
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * ((u : ℝ) + 1) / η)
    refine ⟨k, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hη] at hk
    nlinarith
  have hev : ∀ᶠ n in atTop, ∀ T ∈ TT k,
      |RepRegion.Density.empFreq X n ω T - ((P.map (X 0)) T).toReal| < η / 2 := by
    refine (Filter.eventually_all_finite (hTTf k)).2 fun T hT => ?_
    exact (Metric.tendsto_nhds.1 (hω k T hT) (η / 2) (by positivity)).mono
      fun n hn => by rwa [Real.dist_eq] at hn
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn F hFC hFu => ?_⟩
  have hTn := hN n hn
  choose! sI hsI sO hsO hI hO hOm hIm using hbr k
  have hεpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  obtain ⟨SI, hSI⟩ : ∃ S : Set M, S = ⋃ A ∈ F, sI A := ⟨_, rfl⟩
  obtain ⟨SO, hSO⟩ : ∃ S : Set M, S = ⋃ A ∈ F, sO A := ⟨_, rfl⟩
  have hSIt : SI ⊆ t k := by rw [hSI]; exact Set.iUnion₂_subset fun A hA => hsI A (hFC hA)
  have hSOt : SO ⊆ t k := by rw [hSO]; exact Set.iUnion₂_subset fun A hA => hsO A (hFC hA)
  obtain ⟨I, hIdef⟩ : ∃ I : Set M, I = ⋃ x ∈ SI, Metric.closedBall x (r k) := ⟨_, rfl⟩
  obtain ⟨O, hOdef⟩ : ∃ O : Set M, O = ⋃ x ∈ SO, Metric.closedBall x (r k) := ⟨_, rfl⟩
  have hIT : I ∈ TT k := by rw [hTT]; exact ⟨SI, hSIt, hIdef.symm⟩
  have hOT : O ∈ TT k := by rw [hTT]; exact ⟨SO, hSOt, hOdef.symm⟩
  have hAI : ∀ A ∈ F, (⋃ x ∈ sI A, Metric.closedBall x (r k)) ⊆ I := fun A hA => by
    rw [hIdef]
    exact Set.biUnion_subset_biUnion_left
      (by rw [hSI]; exact Set.subset_iUnion₂ (s := fun A (_ : A ∈ F) => sI A) A hA)
  have hAO : ∀ A ∈ F, (⋃ x ∈ sO A, Metric.closedBall x (r k)) ⊆ O := fun A hA => by
    rw [hOdef]
    exact Set.biUnion_subset_biUnion_left
      (by rw [hSO]; exact Set.subset_iUnion₂ (s := fun A (_ : A ∈ F) => sO A) A hA)
  obtain ⟨U, hU⟩ : ∃ U : Set M, U = ⋃ A ∈ F, A := ⟨_, rfl⟩
  rw [← hU]
  have hIU : I ⊆ U := by
    intro y hy
    rw [hIdef] at hy
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 hy
    rw [hSI] at hx
    obtain ⟨A, hA, hxA⟩ := Set.mem_iUnion₂.1 hx
    rw [hU]
    exact Set.mem_iUnion₂.2 ⟨A, hA, hI A (hFC hA) (Set.mem_iUnion₂.2 ⟨x, hxA, hyx⟩)⟩
  have hUO : U ∩ K ⊆ O := by
    rintro y ⟨hyU, hyK⟩
    rw [hU] at hyU
    obtain ⟨A, hA, hyA⟩ := Set.mem_iUnion₂.1 hyU
    exact hAO A hA (hO A (hFC hA) ⟨hyA, hyK⟩)
  have hOdiff : O \ U ⊆ ⋃ A ∈ F, ((⋃ x ∈ sO A, Metric.closedBall x (r k)) \ A) := by
    rintro y ⟨hyO, hyU⟩
    rw [hOdef] at hyO
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 hyO
    rw [hSO] at hx
    obtain ⟨A, hA, hxA⟩ := Set.mem_iUnion₂.1 hx
    refine Set.mem_iUnion₂.2 ⟨A, hA, Set.mem_iUnion₂.2 ⟨x, hxA, hyx⟩, fun hyA => hyU ?_⟩
    rw [hU]; exact Set.mem_iUnion₂.2 ⟨A, hA, hyA⟩
  have hUdiff : U \ I ⊆ ⋃ A ∈ F, (A \ ⋃ x ∈ sI A, Metric.closedBall x (r k)) := by
    rintro y ⟨hyU, hyI⟩
    rw [hU] at hyU
    obtain ⟨A, hA, hyA⟩ := Set.mem_iUnion₂.1 hyU
    exact Set.mem_iUnion₂.2 ⟨A, hA, hyA, fun h => hyI (hAI A hA h)⟩
  have hcard : (F.card : ℝ) * (1 / ((k : ℝ) + 1)) < η / 2 := by
    have hFu' : (F.card : ℝ) ≤ u := by exact_mod_cast hFu
    calc (F.card : ℝ) * (1 / ((k : ℝ) + 1)) ≤ ((u : ℝ) + 1) * (1 / ((k : ℝ) + 1)) := by
          gcongr; linarith
      _ = ((u : ℝ) + 1) / ((k : ℝ) + 1) := by ring
      _ < η / 2 := hk
  have hsum : ∀ G : Set M → Set M, (∀ A ∈ F, (P.map (X 0)) (G A) ≤
      ENNReal.ofReal (1 / ((k : ℝ) + 1))) →
      ((P.map (X 0)) (⋃ A ∈ F, G A)).toReal ≤ F.card * (1 / ((k : ℝ) + 1)) := by
    intro G hG
    calc ((P.map (X 0)) (⋃ A ∈ F, G A)).toReal
        ≤ (∑ A ∈ F, (P.map (X 0)) (G A)).toReal :=
          ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun A _ => measure_ne_top _ _)
            (measure_biUnion_finset_le F G)
      _ = ∑ A ∈ F, ((P.map (X 0)) (G A)).toReal :=
          ENNReal.toReal_sum (fun A _ => measure_ne_top _ _)
      _ ≤ ∑ A ∈ F, (1 / ((k : ℝ) + 1)) :=
          Finset.sum_le_sum fun A hA => ENNReal.toReal_le_of_le_ofReal hεpos.le (hG A hA)
      _ = F.card * (1 / ((k : ℝ) + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hsplit : ∀ S T : Set M, ((P.map (X 0)) S).toReal ≤
      ((P.map (X 0)) T).toReal + ((P.map (X 0)) (S \ T)).toReal := by
    intro S T
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) ?_
    exact (measure_mono fun y hy => (em (y ∈ T)).elim Or.inl
      (fun h => Or.inr ⟨hy, h⟩)).trans (measure_union_le _ _)
  have hdO : ((P.map (X 0)) (O \ U)).toReal ≤ F.card * (1 / ((k : ℝ) + 1)) :=
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hOdiff)).trans
      (hsum _ fun A hA => hOm A (hFC hA))
  have hdU : ((P.map (X 0)) (U \ I)).toReal ≤ F.card * (1 / ((k : ℝ) + 1)) :=
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hUdiff)).trans
      (hsum _ fun A hA => hIm A (hFC hA))
  have h1 := hsplit O U
  have h2 := hsplit U I
  have he1 : RepRegion.Density.empFreq X n ω U ≤ RepRegion.Density.empFreq X n ω O :=
    emp_mono X n ω fun i _ hi => hUO ⟨hi, hωK i⟩
  have he2 : RepRegion.Density.empFreq X n ω I ≤ RepRegion.Density.empFreq X n ω U :=
    emp_mono X n ω fun i _ hi => hIU hi
  have hO' := abs_lt.1 (hTn O hOT)
  have hI' := abs_lt.1 (hTn I hIT)
  rw [abs_le]
  constructor <;> linarith

/-- L5: average of the density over a region. -/
theorem avg_bound {M : Type*} [MeasurableSpace M] (μ : Measure M) (g : M → ℝ)
    (ν : Measure M) (hdens : ν = μ.withDensity (fun x => ENNReal.ofReal (g x)))
    {A : Set M} (hA : MeasurableSet A) (hpos : 0 < μ A) (hfin : μ A ≠ ⊤)
    {c η : ℝ} (hc : 0 ≤ c) (hη : 0 ≤ η) (hgA : ∀ y ∈ A, |g y - c| ≤ η) :
    |(ν A).toReal / (μ A).toReal - c| ≤ η := by
  subst hdens
  have hν := withDensity_apply (μ := μ) (fun x => ENNReal.ofReal (g x)) hA
  have hμr : 0 < (μ A).toReal := ENNReal.toReal_pos hpos.ne' hfin
  have hup : (μ.withDensity fun x => ENNReal.ofReal (g x)) A ≤ ENNReal.ofReal (c + η) * μ A := by
    rw [hν, ← setLIntegral_const A (ENNReal.ofReal (c + η))]
    exact lintegral_mono_ae ((ae_restrict_iff' hA).2 (Eventually.of_forall fun y hy =>
      ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 (hgA y hy)).2])))
  have hlo : ENNReal.ofReal (c - η) * μ A ≤ (μ.withDensity fun x => ENNReal.ofReal (g x)) A := by
    rw [hν, ← setLIntegral_const A (ENNReal.ofReal (c - η))]
    exact lintegral_mono_ae ((ae_restrict_iff' hA).2 (Eventually.of_forall fun y hy =>
      ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 (hgA y hy)).1])))
  have hfin2 : ENNReal.ofReal (c + η) * μ A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hνfin := ne_top_of_le_ne_top hfin2 hup
  have hup' := ENNReal.toReal_mono hfin2 hup
  have hlo' := ENNReal.toReal_mono hνfin hlo
  rw [ENNReal.toReal_mul] at hup' hlo'
  rw [ENNReal.toReal_ofReal (by linarith)] at hup'
  have h3 : c - η ≤ (ENNReal.ofReal (c - η)).toReal := by
    rw [ENNReal.toReal_ofReal']; exact le_max_left _ _
  have h5 : (c - η) * (μ A).toReal ≤ (ENNReal.ofReal (c - η)).toReal * (μ A).toReal :=
    mul_le_mul_of_nonneg_right h3 hμr.le
  rw [abs_le]; constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hμr]; linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hμr]; linarith

/-- an average of numbers close to `c` is close to `c`. -/
theorem avg_close {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (a : ι → ℝ) (c B : ℝ)
    (h : ∀ i ∈ s, |a i - c| ≤ B) : |(1 / (s.card : ℝ)) * ∑ i ∈ s, a i - c| ≤ B := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have : (1 / (s.card : ℝ)) * ∑ i ∈ s, a i - c = (1 / (s.card : ℝ)) * ∑ i ∈ s, (a i - c) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_sub, one_div, ← mul_assoc,
      inv_mul_cancel₀ hc.ne', one_mul]
  rw [this, abs_mul, abs_of_pos (by positivity)]
  calc (1 / (s.card : ℝ)) * |∑ i ∈ s, (a i - c)| ≤ (1 / (s.card : ℝ)) * ∑ i ∈ s, B := by
        gcongr; exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h)
    _ = B := by
        rw [Finset.sum_const, nsmul_eq_mul, one_div, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

/-- L6+L7: deterministic integral bound at one sample size. -/
theorem core {M Ω : Type*} [MetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (g : M → ℝ) (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (ν : Measure M) [IsProbabilityMeasure ν]
    (hdens : ν = μ.withDensity (fun x => ENNReal.ofReal (g x)))
    (K : Set M) (C : Set (Set M)) (f : Finset M → Finset (Set M))
    (hf : RepRegion.Density.IsRRSMethod C f)
    (hcov : RepRegion.Density.SampleCovering f) (hint : RepRegion.Density.SampleIntersecting f)
    (hCm : ∀ A ∈ C, MeasurableSet A) {γ : ℝ} (hγ : 0 < γ)
    (hγA : ∀ S : Finset M, ∀ A ∈ f S, ENNReal.ofReal γ ≤ μ A)
    (hfin : ∀ S : Finset M, ∀ A ∈ f S, μ A ≠ ⊤)
    (X : ℕ → Ω → M) (n : ℕ) (ω : Ω) (hn : 1 ≤ n) (hK : ∀ i, X i ω ∈ K)
    {η ρ δ e err : ℝ} (hη : 0 ≤ η) (herr : 0 ≤ err)
    (hρ : ∀ s ∈ K, ∀ x, dist x s ≤ ρ → |g x - g s| ≤ η) (heρ : e ≤ ρ) (heδ : e ≤ δ)
    (hdiam : ∀ A ∈ f (RepRegion.Density.sample X n ω), ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ e)
    (hGC1 : ∀ A ∈ f (RepRegion.Density.sample X n ω),
      |RepRegion.Density.empFreq X n ω A - (ν A).toReal| ≤ err)
    (hGCU : |RepRegion.Density.empFreq X n ω
        (RepRegion.Density.coverage f (RepRegion.Density.sample X n ω)) -
      (ν (RepRegion.Density.coverage f (RepRegion.Density.sample X n ω))).toReal| ≤ err) :
    ∫⁻ x, ENNReal.ofReal |g x - RepRegion.Density.ghat μ f X n ω x| ∂μ ≤
      ENNReal.ofReal (2 * η + err / γ) * μ {x | ∃ y ∈ K, dist x y ≤ δ} + ENNReal.ofReal err := by
  classical
  obtain ⟨S, hS⟩ : ∃ S, S = RepRegion.Density.sample X n ω := ⟨_, rfl⟩
  rw [← hS] at hdiam hGC1 hGCU
  obtain ⟨U, hU⟩ : ∃ U, U = RepRegion.Density.coverage f S := ⟨_, rfl⟩
  rw [← hU] at hGCU
  have hUm : MeasurableSet U := by
    rw [hU]; exact Finset.measurableSet_biUnion _ fun A hA => hCm A (hf S A hA)
  have hSK : ∀ s ∈ S, s ∈ K := by
    intro s hs
    rw [hS] at hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
    exact hK i
  have hreg : ∀ A ∈ f S, ∀ x ∈ A,
      |RepRegion.Density.empFreq X n ω A / (μ A).toReal - g x| ≤ 2 * η + err / γ ∧
      x ∈ {x | ∃ y ∈ K, dist x y ≤ δ} := by
    intro A hA x hxA
    obtain ⟨s, hsA, hsS⟩ := hint S A hA
    have hsK := hSK s hsS
    have hγle : γ ≤ (μ A).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal (hfin S A hA)).1 (hγA S A hA)
    have hμr : 0 < (μ A).toReal := lt_of_lt_of_le hγ hγle
    have h2 := avg_bound μ g ν hdens (hCm A (hf S A hA))
      (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hγ) (hγA S A hA)) (hfin S A hA) (hg0 s) hη
      (fun y hy => hρ s hsK y ((hdiam A hA y hy s hsA).trans heρ))
    have h3 := hρ s hsK x ((hdiam A hA x hxA s hsA).trans heρ)
    have h1 : |RepRegion.Density.empFreq X n ω A / (μ A).toReal - (ν A).toReal / (μ A).toReal|
        ≤ err / γ := by
      rw [← sub_div, abs_div, abs_of_pos hμr]
      calc |RepRegion.Density.empFreq X n ω A - (ν A).toReal| / (μ A).toReal
          ≤ err / (μ A).toReal := by gcongr; exact hGC1 A hA
        _ ≤ err / γ := by gcongr
    refine ⟨?_, s, hsK, (hdiam A hA x hxA s hsA).trans heδ⟩
    have h1' := abs_le.1 h1
    have h2' := abs_le.1 h2
    have h3' := abs_le.1 h3
    rw [abs_le]; constructor <;> linarith
  have hpt : ∀ x, ENNReal.ofReal |g x - RepRegion.Density.ghat μ f X n ω x| ≤
      {x | ∃ y ∈ K, dist x y ≤ δ}.indicator (fun _ => ENNReal.ofReal (2 * η + err / γ)) x +
      Uᶜ.indicator (fun x => ENNReal.ofReal (g x)) x := by
    intro x
    unfold RepRegion.Density.ghat
    rw [← hS]
    by_cases hxU : x ∈ U
    · have hxU' := hxU
      rw [hU] at hxU'
      obtain ⟨A, hA, hxA⟩ := Set.mem_iUnion₂.1 hxU'
      have hne : (RepRegion.Density.coverSet f S x).Nonempty := by
        refine ⟨A, ?_⟩
        simp only [RepRegion.Density.coverSet, Finset.mem_filter]
        exact ⟨hA, hxA⟩
      rw [if_neg hne.ne_empty]
      have hb := avg_close _ hne (fun A => RepRegion.Density.empFreq X n ω A / (μ A).toReal) (g x)
        (2 * η + err / γ) (fun B hB => by
          simp only [RepRegion.Density.coverSet, Finset.mem_filter] at hB
          exact (hreg B hB.1 x hB.2).1)
      rw [abs_sub_comm] at hb
      rw [Set.indicator_of_mem (hreg A hA x hxA).2]
      exact le_add_right (ENNReal.ofReal_le_ofReal hb)
    · have hemp : RepRegion.Density.coverSet f S x = ∅ := by
        unfold RepRegion.Density.coverSet
        exact Finset.filter_eq_empty_iff.2 fun A hA hxA =>
          hxU (by rw [hU]; exact Set.mem_iUnion₂.2 ⟨A, hA, hxA⟩)
      rw [if_pos hemp, Set.indicator_of_mem (show x ∈ Uᶜ from hxU), sub_zero,
        abs_of_nonneg (hg0 x)]
      exact le_add_left le_rfl
  have hI2m : Measurable (Uᶜ.indicator (fun x => ENNReal.ofReal (g x))) :=
    (hgm.ennreal_ofReal).indicator hUm.compl
  have hI2 : ∫⁻ x, Uᶜ.indicator (fun x => ENNReal.ofReal (g x)) x ∂μ = ν Uᶜ := by
    rw [lintegral_indicator hUm.compl, hdens, withDensity_apply _ hUm.compl]
  have hemp1 : RepRegion.Density.empFreq X n ω U = 1 := by
    unfold RepRegion.Density.empFreq
    rw [Finset.filter_true_of_mem, Finset.card_range]
    · have : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      exact div_self this
    · intro i hi
      rw [hU]
      apply hcov S
      rw [hS]
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)
  have hνUc : ν Uᶜ ≤ ENNReal.ofReal err := by
    have h1 : ν U + ν Uᶜ = 1 := by rw [measure_add_measure_compl hUm, measure_univ]
    have h2 : (ν U).toReal + (ν Uᶜ).toReal = 1 := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), h1, ENNReal.toReal_one]
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν Uᶜ)]
    apply ENNReal.ofReal_le_ofReal
    rw [hemp1] at hGCU
    have h3 := abs_le.1 hGCU
    linarith [h3.1, h3.2]
  calc ∫⁻ x, ENNReal.ofReal |g x - RepRegion.Density.ghat μ f X n ω x| ∂μ
      ≤ ∫⁻ x, ({x | ∃ y ∈ K, dist x y ≤ δ}.indicator
          (fun _ => ENNReal.ofReal (2 * η + err / γ)) x +
        Uᶜ.indicator (fun x => ENNReal.ofReal (g x)) x) ∂μ := lintegral_mono fun x => hpt x
    _ = ∫⁻ x, {x | ∃ y ∈ K, dist x y ≤ δ}.indicator
          (fun _ => ENNReal.ofReal (2 * η + err / γ)) x ∂μ +
        ∫⁻ x, Uᶜ.indicator (fun x => ENNReal.ofReal (g x)) x ∂μ := lintegral_add_right _ hI2m
    _ ≤ ENNReal.ofReal (2 * η + err / γ) * μ {x | ∃ y ∈ K, dist x y ≤ δ} +
        ENNReal.ofReal err := by
        rw [hI2]; exact add_le_add (lintegral_indicator_const_le _ _) hνUc

end RepRegionD087

open MeasureTheory ProbabilityTheory Filter Topology ENNReal RepRegion.Density in
theorem solution {M Ω Θ : Type*}
    [MetricSpace M] [MeasurableSpace M] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → M)
    (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hball : ∀ (x : M) (r : ℝ), MeasurableSet (Metric.closedBall x r))
    (μ : Measure M) (g : M → ℝ) (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hdens : P.map (X 0) = μ.withDensity (fun x => ENNReal.ofReal (g x)))
    (hgc : Continuous g)
    (K : Set M) (hK : K = supp (P.map (X 0))) (hKc : IsCompact K)
    (hK1 : P.map (X 0) K = 1)
    (hnbhd : ∃ δ : ℝ, 0 < δ ∧ μ {x | ∃ y ∈ K, dist x y ≤ δ} ≠ ⊤)
    (C : Set (Set M)) (R : Θ → ℝ → Set M)
    (hUS : UniformScale C R) (hUC : UnifContWrt C R (P.map (X 0)))
    (f : ℕ → Finset M → Finset (Set M)) (hf : ∀ m, IsRRSMethod C (f m))
    (hAP : ArbitrarilyPrecise P X f)
    (hcov : ∀ m, SampleCovering (f m)) (hint : ∀ m, SampleIntersecting (f m))
    (hcard : ∀ m, AsympBoundedCard P X (f m))
    (hpos : ∀ m, UniformlyPositive C (f m) μ)
    (hfin : ∀ (m : ℕ) (S : Finset M), ∀ A ∈ f m S, μ A ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto (fun m : ℕ => limsup (fun n : ℕ =>
        ∫⁻ x, ENNReal.ofReal |g x - ghat μ (f m) X n ω x| ∂μ) atTop) atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure (P.map (X 0)) :=
    Measure.isProbabilityMeasure_map (hXm 0).aemeasurable
  have hKm : MeasurableSet K := RepRegionD087.isCompact_measurableSet hball hKc
  obtain ⟨δ, hδ, hNfin⟩ := hnbhd
  unfold ArbitrarilyPrecise AsympDiamLE at hAP
  unfold AsympBoundedCard at hcard
  unfold UniformlyPositive at hpos
  have hρ : ∀ k : ℕ, ∃ ρ > 0, ∀ s ∈ K, ∀ x, dist x s ≤ ρ → |g x - g s| ≤ 1 / ((k : ℝ) + 1) :=
    fun k => RepRegionD087.unif_near hgc hKc (by positivity)
  choose ρ hρpos hρ using hρ
  have hN : ∀ k : ℕ, ∃ N : ℕ, ∀ m > N, ∀ᵐ ω ∂P, ∃ N' : ℕ, ∀ n > N',
      ∀ A ∈ f m (sample X n ω), ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ min δ (ρ k) :=
    fun k => hAP _ (lt_min hδ (hρpos k))
  choose Nk hNk using hN
  choose u hu using hcard
  choose hCm γ hγ hγA using hpos
  have hgc_ae := RepRegionD087.gc_union P X hXm hind hid hball hKc hK1 C R hUS hUC
  have hK_ae := RepRegionD087.sample_mem_K P X hXm hid hKm hK1
  have hcard_ae : ∀ᵐ ω ∂P, ∀ m, ∃ N : ℕ, ∀ n > N, (f m (sample X n ω)).card ≤ u m :=
    ae_all_iff.2 hu
  have hdiam_ae : ∀ᵐ ω ∂P, ∀ k m, m > Nk k → ∃ N : ℕ, ∀ n > N,
      ∀ A ∈ f m (sample X n ω), ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ min δ (ρ k) := by
    rw [ae_all_iff]; intro k; rw [ae_all_iff]; intro m
    by_cases hm : m > Nk k
    · exact (hNk k m hm).mono fun ω hω _ => hω
    · exact Eventually.of_forall fun ω h => absurd h hm
  have hB : Tendsto (fun k : ℕ => ENNReal.ofReal (3 * (1 / ((k : ℝ) + 1))) *
      μ {x | ∃ y ∈ K, dist x y ≤ δ} + ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h1
    have h3 : Tendsto (fun k : ℕ => ENNReal.ofReal (3 * (1 / ((k : ℝ) + 1)))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal (h1.const_mul 3)
    have h4 := ENNReal.Tendsto.mul_const h3 (Or.inr hNfin)
    simpa using h4.add h2
  filter_upwards [hgc_ae, hK_ae, hcard_ae, hdiam_ae] with ω hGC hXK hcd hdm
  have hlim : ∀ k : ℕ, ∀ m > Nk k, limsup (fun n : ℕ =>
      ∫⁻ x, ENNReal.ofReal |g x - ghat μ (f m) X n ω x| ∂μ) atTop ≤
      ENNReal.ofReal (3 * (1 / ((k : ℝ) + 1))) * μ {x | ∃ y ∈ K, dist x y ≤ δ} +
        ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    intro k m hm
    have hη : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have herr : 0 < 1 / ((k : ℝ) + 1) * min (γ m) 1 := mul_pos hη (lt_min (hγ m) one_pos)
    have herr1 : 1 / ((k : ℝ) + 1) * min (γ m) 1 ≤ 1 / ((k : ℝ) + 1) :=
      mul_le_of_le_one_right hη.le (min_le_right _ _)
    have herrγ : 1 / ((k : ℝ) + 1) * min (γ m) 1 / γ m ≤ 1 / ((k : ℝ) + 1) := by
      rw [div_le_iff₀ (hγ m)]; exact mul_le_mul_of_nonneg_left (min_le_left _ _) hη.le
    obtain ⟨N1, hN1⟩ := hGC _ herr (max (u m) 1)
    obtain ⟨N2, hN2⟩ := hcd m
    obtain ⟨N3, hN3⟩ := hdm k m hm
    refine limsup_le_of_le (by isBoundedDefault) ?_
    rw [eventually_atTop]
    refine ⟨max (max N1 (N2 + 1)) (max (N3 + 1) 1), fun n hn => ?_⟩
    have hn1 : n ≥ N1 := by omega
    have hn2 : n > N2 := by omega
    have hn3 : n > N3 := by omega
    have hn4 : 1 ≤ n := by omega
    have hGC1 : ∀ A ∈ f m (sample X n ω), |empFreq X n ω A - ((P.map (X 0)) A).toReal| ≤
        1 / ((k : ℝ) + 1) * min (γ m) 1 := by
      intro A hA
      have := hN1 n hn1 {A} (by simpa using hf m _ A hA) (by simp)
      rwa [Finset.set_biUnion_singleton] at this
    have hGCU := hN1 n hn1 (f m (sample X n ω)) (fun A hA => hf m _ A hA)
      ((hN2 n hn2).trans (le_max_left _ _))
    calc ∫⁻ x, ENNReal.ofReal |g x - ghat μ (f m) X n ω x| ∂μ
        ≤ ENNReal.ofReal (2 * (1 / ((k : ℝ) + 1)) + 1 / ((k : ℝ) + 1) * min (γ m) 1 / γ m) *
            μ {x | ∃ y ∈ K, dist x y ≤ δ} + ENNReal.ofReal (1 / ((k : ℝ) + 1) * min (γ m) 1) :=
          RepRegionD087.core μ g hgm hg0 (P.map (X 0)) hdens K C (f m) (hf m) (hcov m) (hint m)
            (hCm m) (hγ m) (hγA m) (hfin m) X n ω hn4 hXK hη.le herr.le (hρ k)
            (min_le_right _ _) (min_le_left _ _) (hN3 n hn3) hGC1 hGCU
      _ ≤ _ := by gcongr <;> linarith
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨k, hk⟩ := ((ENNReal.tendsto_nhds_zero.1 hB) ε hε).exists
  rw [eventually_atTop]
  exact ⟨Nk k + 1, fun m hm => (hlim k m (by omega)).trans hk⟩
