-- Prove2me | solution 1 for SolutionQuality.SRP.prop1_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T05:02:48.327809+00:00
-- url     : https://prove2.me/submissions/09340f3c-6dc5-46cc-b366-e6e6f915696c

import Mathlib
import Definitions.Def_SolutionQuality_SRP_Setting

set_option linter.style.haveILetI false

namespace SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter Topology

/-- Measurability of a `C(K, ℝ)`-valued map from measurability of its evaluations. -/
theorem srpA_measurable_C {Ξ : Type*} [MeasurableSpace Ξ] {K : Type*} [MetricSpace K]
    [CompactSpace K] [MeasurableSpace C(K, ℝ)] [BorelSpace C(K, ℝ)] (F : Ξ → C(K, ℝ)) (hF : ∀ x, Measurable (fun s => F s x)) :
    Measurable F := by
  rcases isEmpty_or_nonempty K with hK | hK
  · exact measurable_of_subsingleton_codomain F
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq K
  have hdist : ∀ t : C(K, ℝ), Measurable (fun s => dist (F s) t) := by
    intro t
    apply measurable_of_Iic
    intro r
    by_cases hr : 0 ≤ r
    · have : (fun s => dist (F s) t) ⁻¹' Set.Iic r =
          ⋂ n, {s | dist (F s (u n)) (t (u n)) ≤ r} := by
        ext s
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter, Set.mem_ofPred_eq]
        constructor
        · intro h n
          exact (ContinuousMap.dist_le hr).1 h (u n)
        · intro h
          refine (ContinuousMap.dist_le hr).2 ?_
          have hcl : IsClosed {x : K | dist (F s x) (t x) ≤ r} :=
            isClosed_le (by fun_prop) continuous_const
          have hsub : Set.range u ⊆ {x : K | dist (F s x) (t x) ≤ r} := by
            rintro _ ⟨n, rfl⟩; exact h n
          have := hcl.closure_subset_iff.2 hsub
          rw [hu.closure_range] at this
          intro x; exact this (Set.mem_univ x)
      rw [this]
      refine MeasurableSet.iInter fun n => ?_
      exact measurableSet_le ((hF _).dist measurable_const) measurable_const
    · have : (fun s => dist (F s) t) ⁻¹' Set.Iic r = ∅ := by
        ext s
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_le]
        exact lt_of_lt_of_le (not_le.1 hr) dist_nonneg
      rw [this]; exact MeasurableSet.empty
  apply measurable_of_isClosed
  intro S hS
  rcases S.eq_empty_or_nonempty with h0 | hne
  · simp [h0]
  obtain ⟨T, hTS, hTc, hST⟩ := (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  have hTne : T.Nonempty := by
    by_contra hT
    rw [Set.not_nonempty_iff_eq_empty] at hT
    rw [hT, closure_empty] at hST
    exact (Set.not_nonempty_iff_eq_empty.2 (Set.subset_empty_iff.1 hST)) hne
  have hinf : ∀ g : C(K, ℝ), Metric.infDist g S = Metric.infDist g T := by
    intro g
    apply le_antisymm
    · exact Metric.infDist_le_infDist_of_subset hTS hTne
    · calc Metric.infDist g T = Metric.infDist g (closure T) := (Metric.infDist_closure).symm
        _ ≤ Metric.infDist g S := Metric.infDist_le_infDist_of_subset hST hne
  have hpre : F ⁻¹' S = (fun s => Metric.infDist (F s) T) ⁻¹' {0} := by
    ext s
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← hinf, ← hS.mem_iff_infDist_zero hne]
  rw [hpre]
  refine (?_ : Measurable (fun s => Metric.infDist (F s) T)) (measurableSet_singleton 0)
  haveI : Countable T := hTc.to_subtype
  haveI : Nonempty T := hTne.to_subtype
  have : (fun s => Metric.infDist (F s) T) = fun s => ⨅ y : T, dist (F s) y := by
    ext s; exact Metric.infDist_eq_iInf
  rw [this]
  exact Measurable.iInf fun y => hdist y


/-- Uniform strong law of large numbers on a compact set, as a.s. convergence in `C(X, ℝ)`. -/
theorem srpA_uslln {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (φ : E d → Ξ → ℝ) (hφm : ∀ x, Measurable (φ x)) (X : Set (E d)) [CompactSpace X]
    (hcont : ∀ᵐ s ∂μ, ContinuousOn (fun x => φ x s) X) (G : Ξ → ℝ) (hG : Integrable G μ)
    (hb : ∀ᵐ s ∂μ, ∀ x ∈ X, |φ x s| ≤ G s)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ) :
    ∃ a : C(X, ℝ), (∀ x : X, a x = expectedCost μ φ x) ∧
      ∀ᵐ ω ∂P, ∃ A : ℕ → C(X, ℝ), Tendsto A atTop (𝓝 a) ∧
        ∀ n (x : X), A n x = sampleMean φ (fun i => ξ i ω) n x := by
  letI : MeasurableSpace C(X, ℝ) := borel _
  haveI : BorelSpace C(X, ℝ) := ⟨rfl⟩
  have hgood : ∀ᵐ s ∂μ, ContinuousOn (fun x => φ x s) X ∧ ∀ x ∈ X, |φ x s| ≤ G s :=
    hcont.and hb
  set N := toMeasurable μ {s | ¬ (ContinuousOn (fun x => φ x s) X ∧ ∀ x ∈ X, |φ x s| ≤ G s)}
    with hNdef
  have hN0 : μ N = 0 := by rw [hNdef, measure_toMeasurable]; exact ae_iff.1 hgood
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hSgood : ∀ s, s ∉ N → ContinuousOn (fun x => φ x s) X ∧ ∀ x ∈ X, |φ x s| ≤ G s := by
    intro s hs
    by_contra h
    exact hs (subset_toMeasurable _ _ h)
  classical
  let F : Ξ → C(X, ℝ) := fun s =>
    if hs : s ∈ N then 0 else ⟨fun x => φ x s, (hSgood s hs).1.domRestrict⟩
  have hFev : ∀ s (x : X), F s x = if s ∈ N then 0 else φ x s := by
    intro s x
    by_cases hs : s ∈ N
    · simp [F, hs]
    · simp only [F, hs, dif_neg, not_false_eq_true, if_false]; rfl
  have hFm : Measurable F := by
    apply srpA_measurable_C F
    intro x
    simp_rw [hFev]
    exact Measurable.ite hNm measurable_const (hφm x)
  have hNae : ∀ᵐ s ∂μ, s ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hFint : Integrable F μ := by
    refine ⟨hFm.aestronglyMeasurable, ContinuousMap.hasFiniteIntegral_of_bound F G hG.2 ?_⟩
    filter_upwards [hNae] with s hs
    intro y
    rw [hFev, if_neg hs, Real.norm_eq_abs]
    exact (hSgood s hs).2 y y.2
  refine ⟨∫ s, F s ∂μ, ?_, ?_⟩
  · intro x
    rw [ContinuousMap.integral_apply hFint]
    unfold expectedCost
    apply integral_congr_ae
    filter_upwards [hNae] with s hs
    rw [hFev, if_neg hs]
  · have hξm := hξ.1
    let Y : ℕ → Ω → C(X, ℝ) := fun i ω => F (ξ i ω)
    have hYint : Integrable (Y 0) P := by
      have h1 : Integrable F (P.map (ξ 0)) := by rw [hξ.2.2 0]; exact hFint
      exact h1.comp_measurable (hξm 0)
    have hindep : Pairwise (Function.onFun (fun A B => IndepFun A B P) Y) := by
      intro i j hij
      exact (hξ.2.1.comp (fun _ => F) (fun _ => hFm)).indepFun hij
    have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := by
      intro i
      refine ⟨(hFm.comp (hξm i)).aemeasurable, (hFm.comp (hξm 0)).aemeasurable, ?_⟩
      show P.map (F ∘ ξ i) = P.map (F ∘ ξ 0)
      rw [← Measure.map_map hFm (hξm i), ← Measure.map_map hFm (hξm 0), hξ.2.2 i, hξ.2.2 0]
    have hslln := strong_law_ae Y hYint hindep hident
    have hlim : ∫ ω, Y 0 ω ∂P = ∫ s, F s ∂μ := by
      rw [← hξ.2.2 0, integral_map (hξm 0).aemeasurable]
      rw [hξ.2.2 0]; exact hFm.aestronglyMeasurable
    have hall : ∀ᵐ ω ∂P, ∀ i, ξ i ω ∉ N := by
      refine ae_all_iff.2 fun i => ?_
      have : P (ξ i ⁻¹' N) = 0 := by
        rw [← Measure.map_apply (hξm i) hNm, hξ.2.2 i]; exact hN0
      exact measure_eq_zero_iff_ae_notMem.1 this
    filter_upwards [hslln, hall] with ω hω hω'
    refine ⟨fun n => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Y i ω, ?_, ?_⟩
    · rw [← hlim]; exact hω
    · intro n x
      simp only [ContinuousMap.smul_apply, ContinuousMap.coe_sum, Finset.sum_apply, smul_eq_mul]
      unfold sampleMean
      rw [one_div]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      show F (ξ i ω) x = _
      rw [hFev, if_neg (hω' i)]

end SolutionQuality.SRP


namespace SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter Topology

theorem srpB_tuo {d : ℕ} {X : Set (E d)} [CompactSpace X] (A : ℕ → C(X, ℝ)) (a : C(X, ℝ))
    (u : ℕ → E d → ℝ) (v : E d → ℝ) (hA : Tendsto A atTop (𝓝 a))
    (hu : ∀ n (x : X), A n x = u n x) (hv : ∀ x : X, a x = v x) :
    TendstoUniformlyOn u v atTop X := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have h := ContinuousMap.tendsto_iff_tendstoUniformly.1 hA
  have e1 : (fun n (x : X) => u n x) = fun n => (A n : X → ℝ) := by
    funext n x; exact (hu n x).symm
  have e2 : (fun x : X => v x) = (a : X → ℝ) := by funext x; exact (hv x).symm
  simpa [Function.comp_def, e1, e2] using h

/-- Envelope from (A2): `|f x s| ≤ 1 + |g s|` and `f x s ^ 2 ≤ |g s|` on `X`. -/
theorem srpB_env {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (f : E d → Ξ → ℝ) (X : Set (E d)) (hA : Assumptions μ f X) :
    ∃ g : Ξ → ℝ, Integrable g μ ∧ (∀ s, 0 ≤ g s) ∧ ∀ᵐ s ∂μ, ∀ x ∈ X, f x s ^ 2 ≤ g s := by
  obtain ⟨g, hg, hgb⟩ := hA.A2
  refine ⟨fun s => |g s|, hg.abs, fun s => abs_nonneg _, ?_⟩
  filter_upwards [hgb] with s hs x hx
  exact (hs x hx).trans (le_abs_self _)

theorem srpB_abs_le {a b : ℝ} (h : a ^ 2 ≤ b) : |a| ≤ 1 + b := by
  have : |a| ^ 2 = a ^ 2 := sq_abs a
  nlinarith [abs_nonneg a, sq_nonneg (|a| - 1)]

theorem srpB_fbar_C {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) [CompactSpace X] (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ) :
    ∃ a : C(X, ℝ), (∀ x : X, a x = expectedCost μ f x) ∧
      ∀ᵐ ω ∂P, ∃ A : ℕ → C(X, ℝ), Tendsto A atTop (𝓝 a) ∧
        ∀ n (x : X), A n x = sampleMean f (fun i => ξ i ω) n x := by
  obtain ⟨g, hg, hg0, hgb⟩ := srpB_env μ f X hA
  refine srpA_uslln μ f hfm X hA.A1 (fun s => 1 + g s) ((integrable_const 1).add hg) ?_ P ξ hξ
  filter_upwards [hgb] with s hs x hx
  exact srpB_abs_le (hs x hx)

theorem srpB_fbar {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn (fun n x => sampleMean f (fun i => ξ i ω) n x)
      (expectedCost μ f) atTop X := by
  haveI : CompactSpace X := isCompact_iff_compactSpace.mp hA.A3.2
  obtain ⟨a, ha, hae⟩ := srpB_fbar_C μ f hfm X hA P ξ hξ
  filter_upwards [hae] with ω ⟨A, hA1, hA2⟩
  exact srpB_tuo A a _ _ hA1 hA2 ha

/-- Algebraic identity for the sample variance. -/
theorem srpB_var_identity (n : ℕ) (y : ℕ → ℝ) :
    (1 / ((n : ℝ) - 1)) * ∑ i ∈ Finset.range n, (y i - (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, y j) ^ 2
      = ((n : ℝ) / ((n : ℝ) - 1)) *
        ((1 / (n : ℝ)) * ∑ i ∈ Finset.range n, (y i) ^ 2 -
          ((1 / (n : ℝ)) * ∑ j ∈ Finset.range n, y j) ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set S := ∑ j ∈ Finset.range n, y j with hS
  set M := (1 / (n : ℝ)) * S with hM
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hSM : S = n * M := by rw [hM]; field_simp
  have : ∑ i ∈ Finset.range n, (y i - M) ^ 2 =
      ∑ i ∈ Finset.range n, (y i) ^ 2 - 2 * M * S + n * M ^ 2 := by
    have e : ∀ i, (y i - M) ^ 2 = (y i) ^ 2 - 2 * M * y i + M ^ 2 := fun i => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, hS]
  rw [this, hSM]
  field_simp
  ring

theorem srpB_sampleVar_eq {d : ℕ} {Ξ : Type*} (f : E d → Ξ → ℝ) (xhat : E d) (s : ℕ → Ξ)
    (n : ℕ) (x : E d) :
    sampleVar f xhat s n x = ((n : ℝ) / ((n : ℝ) - 1)) *
      (sampleMean (fun x s => (f xhat s - f x s) ^ 2) s n x -
        (sampleMean (fun x s => f xhat s - f x s) s n x) ^ 2) := by
  have h1 : sampleMean f s n xhat - sampleMean f s n x =
      sampleMean (fun x s => f xhat s - f x s) s n x := by
    unfold sampleMean; rw [← mul_sub, ← Finset.sum_sub_distrib]
  unfold sampleVar
  rw [h1]
  unfold sampleMean
  exact srpB_var_identity n (fun i => f xhat (s i) - f x (s i))

theorem srpB_var_C {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) [CompactSpace X] (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (xhat : E d) (hxhat : xhat ∈ X) :
    ∃ a : C(X, ℝ), (∀ x : X, a x = gapVar μ f xhat x) ∧
      ∀ᵐ ω ∂P, ∃ A : ℕ → C(X, ℝ), Tendsto A atTop (𝓝 a) ∧
        ∀ n (x : X), A n x = sampleVar f xhat (fun i => ξ i ω) n x := by
  obtain ⟨g, hg, hg0, hgb⟩ := srpB_env μ f X hA
  set φ1 : E d → Ξ → ℝ := fun x s => f xhat s - f x s with hφ1
  set φ2 : E d → Ξ → ℝ := fun x s => (f xhat s - f x s) ^ 2 with hφ2
  have hφ1m : ∀ x, Measurable (φ1 x) := fun x => (hfm xhat).sub (hfm x)
  have hφ2m : ∀ x, Measurable (φ2 x) := fun x => ((hfm xhat).sub (hfm x)).pow_const 2
  have hc1 : ∀ᵐ s ∂μ, ContinuousOn (fun x => φ1 x s) X := by
    filter_upwards [hA.A1] with s hs
    exact continuousOn_const.sub hs
  have hc2 : ∀ᵐ s ∂μ, ContinuousOn (fun x => φ2 x s) X := by
    filter_upwards [hc1] with s hs
    exact hs.pow 2
  have hb2 : ∀ᵐ s ∂μ, ∀ x ∈ X, |φ2 x s| ≤ 4 * g s := by
    filter_upwards [hgb] with s hs x hx
    have h1 := hs xhat hxhat
    have h2 := hs x hx
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (f xhat s + f x s)]
  have hb1 : ∀ᵐ s ∂μ, ∀ x ∈ X, |φ1 x s| ≤ 1 + 4 * g s := by
    filter_upwards [hb2] with s hs x hx
    have := hs x hx
    rw [abs_of_nonneg (sq_nonneg _)] at this
    exact srpB_abs_le this
  obtain ⟨a1, ha1, hae1⟩ := srpA_uslln μ φ1 hφ1m X hc1 (fun s => 1 + 4 * g s)
    ((integrable_const 1).add (hg.const_mul 4)) hb1 P ξ hξ
  obtain ⟨a2, ha2, hae2⟩ := srpA_uslln μ φ2 hφ2m X hc2 (fun s => 4 * g s)
    (hg.const_mul 4) hb2 P ξ hξ
  refine ⟨a2 - a1 * a1, ?_, ?_⟩
  · intro x
    have hmem : MemLp (φ1 x) 2 μ := by
      refine (memLp_two_iff_integrable_sq (hφ1m x).aestronglyMeasurable).2 ?_
      refine Integrable.mono' (hg.const_mul 4) ((hφ2m x).aestronglyMeasurable) ?_
      filter_upwards [hb2] with s hs
      rw [Real.norm_eq_abs]
      exact hs x x.2
    simp only [ContinuousMap.sub_apply, ContinuousMap.mul_apply]
    rw [ha1, ha2]
    unfold gapVar expectedCost
    rw [variance_eq_sub hmem]
    simp only [Pi.pow_apply, hφ1, hφ2]
    ring
  · filter_upwards [hae1, hae2] with ω ⟨A1, hA1, hA1e⟩ ⟨A2, hA2, hA2e⟩
    refine ⟨fun n => ((n : ℝ) / ((n : ℝ) - 1)) • (A2 n - A1 n * A1 n), ?_, ?_⟩
    · have hc : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1)) atTop (𝓝 1) := by
        have h1 : Tendsto (fun n : ℕ => 1 / (1 - 1 / (n : ℝ))) atTop (𝓝 (1 / (1 - 0))) := by
          refine tendsto_const_nhds.div (tendsto_const_nhds.sub ?_) (by norm_num)
          exact tendsto_one_div_atTop_nhds_zero_nat
        simp only [sub_zero, div_one] at h1
        refine h1.congr' ?_
        filter_upwards [eventually_ge_atTop 2] with n hn
        have : (n : ℝ) ≥ 2 := by exact_mod_cast hn
        field_simp
      have : Tendsto (fun n : ℕ => ((n : ℝ) / ((n : ℝ) - 1)) • (A2 n - A1 n * A1 n)) atTop
          (𝓝 ((1 : ℝ) • (a2 - a1 * a1))) := Tendsto.smul hc (hA2.sub (hA1.mul hA1))
      simpa using this
    · intro n x
      simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.mul_apply,
        smul_eq_mul]
      rw [hA1e, hA2e, srpB_sampleVar_eq]
      ring

theorem srpB_sampleVar {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (xhat : E d) (hxhat : xhat ∈ X) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn (fun n x => sampleVar f xhat (fun i => ξ i ω) n x)
      (gapVar μ f xhat) atTop X := by
  haveI : CompactSpace X := isCompact_iff_compactSpace.mp hA.A3.2
  obtain ⟨a, ha, hae⟩ := srpB_var_C μ f hfm X hA P ξ hξ xhat hxhat
  filter_upwards [hae] with ω ⟨A, hA1, hA2⟩
  exact srpB_tuo A a _ _ hA1 hA2 ha

end SolutionQuality.SRP


namespace SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter Topology

theorem srpC_reindex {α : Type*} {u : ℕ → α → ℝ} {v : α → ℝ} {s : Set α}
    (hu : TendstoUniformlyOn u v atTop s) {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) :
    TendstoUniformlyOn (fun k => u (ψ k)) v atTop s :=
  fun U hU => hψ.eventually (hu U hU)

/-- Limits of (subsequences of) SAA minimizers minimize the uniform limit. -/
theorem srpC_opt {d : ℕ} {X : Set (E d)} (hXc : IsClosed X) (Ef : E d → ℝ)
    (hEf : ContinuousOn Ef X) (u : ℕ → E d → ℝ) (hu : TendstoUniformlyOn u Ef atTop X)
    (z : ℕ → E d) (hz : ∀ n, z n ∈ X ∧ ∀ y ∈ X, u n (z n) ≤ u n y)
    (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop) (x : E d)
    (hx : Tendsto (fun k => z (ψ k)) atTop (𝓝 x)) :
    x ∈ X ∧ ∀ y ∈ X, Ef x ≤ Ef y := by
  have hxX : x ∈ X := hXc.mem_of_tendsto hx (Eventually.of_forall fun k => (hz (ψ k)).1)
  refine ⟨hxX, fun y hy => ?_⟩
  have hu' := srpC_reindex hu hψ
  have h1 : Tendsto (fun k => u (ψ k) (z (ψ k))) atTop (𝓝 (Ef x)) :=
    hu'.tendsto_comp (hEf x hxX)
      (tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall fun k => (hz (ψ k)).1⟩)
  have h2 : Tendsto (fun k => u (ψ k) y) atTop (𝓝 (Ef y)) := hu'.tendsto_at hy
  exact le_of_tendsto_of_tendsto' h1 h2 fun k => (hz (ψ k)).2 y hy

theorem srpC_contOn_of_C {d : ℕ} {X : Set (E d)} (a : C(X, ℝ)) (v : E d → ℝ)
    (ha : ∀ x : X, a x = v x) : ContinuousOn v X := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : X.domRestrict v = a := by funext x; exact (ha x).symm
  rw [this]; exact a.continuous

theorem srpC_sInf_lip {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (g h : C(K, ℝ)) : sInf (Set.range g) - dist g h ≤ sInf (Set.range h) := by
  have hb : BddBelow (Set.range g) := (isCompact_range g.continuous).bddBelow
  refine le_csInf (Set.range_nonempty h) ?_
  rintro _ ⟨x, rfl⟩
  have h1 : g x - h x ≤ dist g h := by
    have := ContinuousMap.dist_apply_le_dist (f := g) (g := h) x
    rw [Real.dist_eq] at this
    exact (le_abs_self _).trans this
  have h2 : sInf (Set.range g) ≤ g x := csInf_le hb ⟨x, rfl⟩
  linarith

theorem srpC_prop1_i {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ) :
    ∀ᵐ ω ∂P, Tendsto (fun n => saaValue f X (fun i => ξ i ω) n) atTop
      (𝓝 (optValue μ f X)) := by
  haveI : CompactSpace X := isCompact_iff_compactSpace.mp hA.A3.2
  haveI : Nonempty X := hA.A3.1.to_subtype
  obtain ⟨a, ha, hae⟩ := srpB_fbar_C μ f hfm X hA P ξ hξ
  filter_upwards [hae] with ω ⟨A, hA1, hA2⟩
  have e1 : ∀ n, saaValue f X (fun i => ξ i ω) n = sInf (Set.range (A n)) := by
    intro n
    unfold saaValue
    rw [Set.image_eq_range]
    congr 1
    ext t; simp only [Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, hA2 n x⟩
    · rintro ⟨x, rfl⟩; exact ⟨x, (hA2 n x).symm⟩
  have e2 : optValue μ f X = sInf (Set.range a) := by
    unfold optValue
    rw [Set.image_eq_range]
    congr 1
    ext t; simp only [Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, ha x⟩
    · rintro ⟨x, rfl⟩; exact ⟨x, (ha x).symm⟩
  simp_rw [e1, e2]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hA1 ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h1 := srpC_sInf_lip (A n) a
  have h2 := srpC_sInf_lip a (A n)
  rw [dist_comm a] at h2
  have h3 := hN n hn
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem srpC_prop1_ii {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (xn : ℕ → Ω → E d) (hxn : IsSAAMinimizerSeq P f X ξ xn) :
    ∀ᵐ ω ∂P, ∀ x, MapClusterPt x atTop (fun n => xn n ω) → x ∈ optSet μ f X := by
  haveI : CompactSpace X := isCompact_iff_compactSpace.mp hA.A3.2
  obtain ⟨a, ha, -⟩ := srpB_fbar_C μ f hfm X hA P ξ hξ
  have hEf := srpC_contOn_of_C a _ ha
  filter_upwards [srpB_fbar μ f hfm X hA P ξ hξ, ae_all_iff.2 hxn.2] with ω hu hmin
  intro x hx
  obtain ⟨ψ, hψm, hψ⟩ := hx.tendsto_subseq
  exact srpC_opt hA.A3.2.isClosed _ hEf _ hu _ hmin ψ hψm.tendsto_atTop x hψ

theorem srpC_prop1_iii {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (xhat : E d) (hxhat : xhat ∈ X)
    (xn : ℕ → Ω → E d) (hxn : IsSAAMinimizerSeq P f X ξ xn)
    (xmin xmax : E d)
    (hxmin : xmin ∈ optSet μ f X ∧ ∀ x ∈ optSet μ f X, gapVar μ f xhat xmin ≤ gapVar μ f xhat x)
    (hxmax : xmax ∈ optSet μ f X ∧ ∀ x ∈ optSet μ f X, gapVar μ f xhat x ≤ gapVar μ f xhat xmax) :
    ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n in atTop,
      gapVar μ f xhat xmin - ε ≤ sampleVar f xhat (fun i => ξ i ω) n (xn n ω) ∧
        sampleVar f xhat (fun i => ξ i ω) n (xn n ω) ≤ gapVar μ f xhat xmax + ε := by
  haveI : CompactSpace X := isCompact_iff_compactSpace.mp hA.A3.2
  obtain ⟨a, ha, -⟩ := srpB_fbar_C μ f hfm X hA P ξ hξ
  have hEf := srpC_contOn_of_C a _ ha
  obtain ⟨v, hv, hvae⟩ := srpB_var_C μ f hfm X hA P ξ hξ xhat hxhat
  have hvc := srpC_contOn_of_C v _ hv
  have hXc := hA.A3.2
  filter_upwards [srpB_fbar μ f hfm X hA P ξ hξ, ae_all_iff.2 hxn.2, hvae] with ω hu hmin
    ⟨V, hV, hVe⟩
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have key_lo : ∀ᶠ n in atTop, gapVar μ f xhat xmin - ε / 2 ≤ gapVar μ f xhat (xn n ω) := by
    by_contra h
    rw [not_eventually] at h
    simp only [not_le] at h
    obtain ⟨ψ, hψm, hψ⟩ := extraction_of_frequently_atTop h
    obtain ⟨x, hxX, φ, hφm, hφ⟩ :=
      hXc.tendsto_subseq (x := fun k => xn (ψ k) ω) (fun k => (hmin (ψ k)).1)
    have hopt := srpC_opt hXc.isClosed _ hEf _ hu _ hmin (ψ ∘ φ)
      (hψm.tendsto_atTop.comp hφm.tendsto_atTop) x hφ
    have hlim : Tendsto (fun k => gapVar μ f xhat (xn (ψ (φ k)) ω)) atTop
        (𝓝 (gapVar μ f xhat x)) :=
      (hvc x hxX).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hφ, Eventually.of_forall fun k => (hmin _).1⟩)
    have h1 : gapVar μ f xhat x ≤ gapVar μ f xhat xmin - ε / 2 :=
      le_of_tendsto' hlim fun k => (hψ (φ k)).le
    have h2 := hxmin.2 x hopt
    linarith
  have key_hi : ∀ᶠ n in atTop, gapVar μ f xhat (xn n ω) ≤ gapVar μ f xhat xmax + ε / 2 := by
    by_contra h
    rw [not_eventually] at h
    simp only [not_le] at h
    obtain ⟨ψ, hψm, hψ⟩ := extraction_of_frequently_atTop h
    obtain ⟨x, hxX, φ, hφm, hφ⟩ :=
      hXc.tendsto_subseq (x := fun k => xn (ψ k) ω) (fun k => (hmin (ψ k)).1)
    have hopt := srpC_opt hXc.isClosed _ hEf _ hu _ hmin (ψ ∘ φ)
      (hψm.tendsto_atTop.comp hφm.tendsto_atTop) x hφ
    have hlim : Tendsto (fun k => gapVar μ f xhat (xn (ψ (φ k)) ω)) atTop
        (𝓝 (gapVar μ f xhat x)) :=
      (hvc x hxX).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hφ, Eventually.of_forall fun k => (hmin _).1⟩)
    have h1 : gapVar μ f xhat xmax + ε / 2 ≤ gapVar μ f xhat x :=
      ge_of_tendsto' hlim fun k => (hψ (φ k)).le
    have h2 := hxmax.2 x hopt
    linarith
  have hclose : ∀ᶠ n in atTop, dist (V n) v < ε / 2 :=
    hV.eventually (Metric.ball_mem_nhds v hε2)
  filter_upwards [key_lo, key_hi, hclose] with n h1 h2 h3
  have h4 := ContinuousMap.dist_apply_le_dist (f := V n) (g := v) ⟨xn n ω, (hmin n).1⟩
  rw [hVe, hv, Real.dist_eq] at h4
  have h5 := abs_lt.1 (lt_of_le_of_lt h4 h3)
  constructor <;> linarith [h5.1, h5.2]

end SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter SolutionQuality.SRP

theorem solution {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (xn : ℕ → Ω → E d) (hxn : IsSAAMinimizerSeq P f X ξ xn) :
    ∀ᵐ ω ∂P, ∀ x, MapClusterPt x atTop (fun n => xn n ω) → x ∈ optSet μ f X :=
  srpC_prop1_ii μ f hfm X hA P ξ hξ xn hxn
