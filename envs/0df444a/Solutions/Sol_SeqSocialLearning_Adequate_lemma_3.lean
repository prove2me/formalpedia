-- Prove2me | solution 1 for SeqSocialLearning.Adequate.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T09:55:33.971681+00:00
-- url     : https://prove2.me/submissions/1f295b8b-a576-44af-9ab5-436ad327adf6

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace SSLLem3Aux

open scoped ENNReal

/-- Lusin's theorem for maps into a second-countable space. -/
lemma lusin {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  classical
  set B := TopologicalSpace.countableBasis Y
  have hBc : B.Countable := TopologicalSpace.countable_countableBasis Y
  have hBb := TopologicalSpace.isBasis_countableBasis Y
  have : Countable B := hBc.to_subtype
  have hε2 : ε / 2 ≠ 0 := by simpa using hε
  obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable hε2 B
  -- compact sets inside `f ⁻¹' b` and its complement
  have hP : ∀ b : B, MeasurableSet (f ⁻¹' (b : Set Y)) :=
    fun b => hf (hBb.isOpen b.2).measurableSet
  have hpos : ∀ b : B, ((ε' b : ℝ≥0∞) / 2) ≠ 0 := fun b => by
    simpa using (hε'pos b).ne'
  choose K hKsub hKc hKμ using fun b : B =>
    (hP b).exists_isCompact_sdiff_lt (measure_ne_top μ _) (hpos b)
  choose L hLsub hLc hLμ using fun b : B =>
    (hP b).compl.exists_isCompact_sdiff_lt (measure_ne_top μ _) (hpos b)
  obtain ⟨K0, -, hK0c, hK0μ⟩ :=
    MeasurableSet.univ.exists_isCompact_sdiff_lt (μ := μ) (measure_ne_top μ _) hε2
  refine ⟨K0 ∩ ⋂ b : B, (K b ∪ L b), ?_, ?_, ?_⟩
  · exact hK0c.inter_right (isClosed_iInter fun b => ((hKc b).union (hLc b)).isClosed)
  · have hMb : ∀ b : B, μ (K b ∪ L b)ᶜ ≤ ε' b := by
      intro b
      have : (K b ∪ L b)ᶜ ⊆ (f ⁻¹' (b : Set Y) \ K b) ∪ ((f ⁻¹' (b : Set Y))ᶜ \ L b) := by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_union, not_or] at hx
        by_cases h : x ∈ f ⁻¹' (b : Set Y)
        · exact Or.inl ⟨h, hx.1⟩
        · exact Or.inr ⟨h, hx.2⟩
      calc μ (K b ∪ L b)ᶜ ≤ μ (f ⁻¹' (b : Set Y) \ K b) + μ ((f ⁻¹' (b : Set Y))ᶜ \ L b) :=
            (measure_mono this).trans (measure_union_le _ _)
        _ ≤ ε' b / 2 + ε' b / 2 := add_le_add (hKμ b).le (hLμ b).le
        _ = ε' b := ENNReal.add_halves _
    rw [Set.compl_inter, Set.compl_iInter]
    calc μ (K0ᶜ ∪ ⋃ b : B, (K b ∪ L b)ᶜ) ≤ μ K0ᶜ + μ (⋃ b : B, (K b ∪ L b)ᶜ) :=
          measure_union_le _ _
      _ ≤ μ K0ᶜ + ∑' b : B, μ (K b ∪ L b)ᶜ := add_le_add le_rfl (measure_iUnion_le _)
      _ ≤ μ K0ᶜ + ∑' b : B, (ε' b : ℝ≥0∞) := add_le_add le_rfl (ENNReal.tsum_le_tsum hMb)
      _ < ε / 2 + ε / 2 := by
          rw [Set.compl_eq_univ_sdiff]
          exact ENNReal.add_lt_add hK0μ hε'sum
      _ = ε := ENNReal.add_halves _
  · rw [continuousOn_iff']
    intro t ht
    refine ⟨⋃ b : {b : B // (b : Set Y) ⊆ t}, (L b.1)ᶜ,
      isOpen_iUnion fun b => (hLc b.1).isClosed.isOpen_compl, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, Set.mem_compl_iff,
      Set.mem_iInter, Set.mem_union]
    constructor
    · rintro ⟨hxt, hx0, hxM⟩
      obtain ⟨b, hb, hxb, hbt⟩ := hBb.exists_subset_of_mem_open hxt ht
      refine ⟨⟨⟨⟨b, hb⟩, hbt⟩, fun hL => ?_⟩, hx0, hxM⟩
      exact hLsub ⟨b, hb⟩ hL hxb
    · rintro ⟨⟨⟨b, hbt⟩, hxL⟩, hx0, hxM⟩
      refine ⟨?_, hx0, hxM⟩
      rcases hxM b with hK | hL
      · exact hbt (hKsub b hK)
      · exact absurd hL hxL

/-- The section map `ω ↦ u(·, ω)` into `C(A, ℝ)` is Borel measurable. -/
lemma measurable_section {Ω A : Type*} [MeasurableSpace Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nonempty A]
    (u : A → Ω → ℝ) (hmeas : Measurable (Function.uncurry u)) (hcont : ∀ ω, Continuous fun a => u a ω) :
    @Measurable _ _ _ (borel C(A, ℝ)) (fun ω => (⟨fun a => u a ω, hcont ω⟩ : C(A, ℝ))) := by
  letI : MeasurableSpace C(A, ℝ) := borel _
  haveI : BorelSpace C(A, ℝ) := ⟨rfl⟩
  set Φ : Ω → C(A, ℝ) := fun ω => ⟨fun a => u a ω, hcont ω⟩
  set d := TopologicalSpace.denseSeq A
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq A
  have hk : ∀ a : A, Measurable fun ω => u a ω := fun a =>
    hmeas.comp (measurable_const.prodMk measurable_id)
  -- preimages of open balls
  have hball : ∀ (g : C(A, ℝ)) (q : ℝ), MeasurableSet (Φ ⁻¹' Metric.ball g q) := by
    intro g q
    have : Φ ⁻¹' Metric.ball g q =
        ⋃ n : ℕ, ⋂ k : ℕ, {ω | |u (d k) ω - g (d k)| ≤ q - 1 / ((n : ℝ) + 1)} := by
      ext ω
      simp only [Set.mem_preimage, Metric.mem_ball, Set.mem_iUnion, Set.mem_iInter,
        Set.mem_ofPred_eq]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
        refine ⟨n, fun k => ?_⟩
        have := ContinuousMap.dist_apply_le_dist (f := Φ ω) (g := g) (d k)
        rw [Real.dist_eq] at this
        have : (1 : ℝ) / (n + 1) ≤ q - dist (Φ ω) g := hn.le
        simp only [Φ, ContinuousMap.coe_mk] at *
        linarith
      · rintro ⟨n, hn⟩
        set c := q - 1 / ((n : ℝ) + 1)
        have hall : ∀ a, |u a ω - g a| ≤ c := by
          have hcl : IsClosed {a : A | |u a ω - g a| ≤ c} :=
            isClosed_le (((hcont ω).sub g.continuous).abs) continuous_const
          have : Set.range d ⊆ {a : A | |u a ω - g a| ≤ c} := by
            rintro _ ⟨k, rfl⟩; exact hn k
          have h2 := hcl.closure_subset_iff.2 this
          rw [hd.closure_range] at h2
          exact fun a => h2 (Set.mem_univ a)
        have hc0 : 0 ≤ c := (abs_nonneg _).trans (hall (Classical.arbitrary A))
        have : dist (Φ ω) g ≤ c := by
          rw [ContinuousMap.dist_le hc0]
          intro a
          rw [Real.dist_eq]
          exact hall a
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    rw [this]
    refine MeasurableSet.iUnion fun n => MeasurableSet.iInter fun k => ?_
    exact measurableSet_le (((hk (d k)).sub measurable_const).abs) measurable_const
  refine measurable_of_isOpen fun U hU => ?_
  let ι := {p : C(A, ℝ) × ℚ // Metric.ball p.1 (p.2 : ℝ) ⊆ U}
  have hUeq : U = ⋃ i : ι, Metric.ball i.1.1 (i.1.2 : ℝ) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
      obtain ⟨q, hq0, hqr⟩ := exists_rat_btwn hr
      exact Set.mem_iUnion.2 ⟨⟨(x, q), (Metric.ball_subset_ball hqr.le).trans hrU⟩,
        Metric.mem_ball_self (by exact_mod_cast hq0)⟩
    · exact Set.iUnion_subset fun i => i.2
  obtain ⟨T, hT, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : ι => Metric.ball i.1.1 (i.1.2 : ℝ)) (fun i => Metric.isOpen_ball)
  rw [hUeq, ← hTeq, Set.preimage_iUnion₂]
  exact MeasurableSet.biUnion hT fun i _ => hball _ _

end SSLLem3Aux

open SeqSocialLearning.Adequate SSLLem3Aux

theorem solution {Ω A : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : A → Ω → ℝ) (hu : InU u) (ε γ : ℝ) (hε : 0 < ε) (hγ : 0 < γ) :
    ∃ E : Set Ω, IsCompact E ∧ 1 - ε ≤ μ.real E ∧
      ∃ η β : ℝ, 0 < η ∧ 0 < β ∧
        ∀ ω ∈ E, ∀ ω' ∈ E, ∀ a a' : A, dist ω ω' ≤ β → dist a a' ≤ η →
          |u a ω - u a' ω'| ≤ γ := by
  obtain ⟨hmeas, -, hcont⟩ := hu
  letI : MeasurableSpace C(A, ℝ) := borel _
  haveI : BorelSpace C(A, ℝ) := ⟨rfl⟩
  set Φ : Ω → C(A, ℝ) := fun ω => ⟨fun a => u a ω, hcont ω⟩ with hΦ
  have hΦm : Measurable Φ := measurable_section u hmeas hcont
  obtain ⟨K, hKc, hKμ, hKcont⟩ := lusin μ Φ hΦm (ε := ENNReal.ofReal ε) (by simpa using hε)
  refine ⟨K, hKc, ?_, ?_⟩
  · have h1 : μ.real Kᶜ < ε := by
      rw [measureReal_def]
      exact (ENNReal.toReal_lt_of_lt_ofReal hKμ)
    have h2 : μ.real Kᶜ = 1 - μ.real K := by
      rw [probReal_compl_eq_one_sub (hKc.isClosed.measurableSet)]
    linarith
  · -- joint continuity of `(ω, a) ↦ u a ω` on `K × A`
    set G : Ω × A → ℝ := fun p => Φ p.1 p.2
    have hG : ContinuousOn G (K ×ˢ Set.univ) := by
      have h1 : ContinuousOn (fun p : Ω × A => (Φ p.1, p.2)) (K ×ˢ Set.univ) :=
        (hKcont.comp continuousOn_fst (fun p hp => hp.1)).prodMk continuousOn_snd
      exact continuous_eval.comp_continuousOn h1
    have hcpt : IsCompact (K ×ˢ (Set.univ : Set A)) := hKc.prod isCompact_univ
    have huc := hcpt.uniformContinuousOn_of_continuous hG
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ, hδG⟩ := huc γ hγ
    refine ⟨δ / 2, δ / 2, by positivity, by positivity, ?_⟩
    intro ω hω ω' hω' a a' hωω' haa'
    have hdist : dist (ω, a) (ω', a') < δ := by
      rw [Prod.dist_eq]
      exact max_lt (by linarith) (by linarith)
    have := hδG (ω, a) ⟨hω, Set.mem_univ _⟩ (ω', a') ⟨hω', Set.mem_univ _⟩ hdist
    rw [Real.dist_eq] at this
    exact this.le
