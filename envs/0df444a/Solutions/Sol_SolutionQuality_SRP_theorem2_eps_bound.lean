-- Prove2me | solution 1 for SolutionQuality.SRP.theorem2_eps_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T05:13:56.595264+00:00
-- url     : https://prove2.me/submissions/434e3430-f89c-46b7-ad1f-170de1fe6031

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

end SolutionQuality.SRP


namespace SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter Topology

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


namespace SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter Topology

theorem srpD_ae_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Set Ω) (hS : ∀ᵐ ω ∂P, ω ∈ S) : P S = 1 := by
  apply le_antisymm prob_le_one
  have h0 : P Sᶜ = 0 := by
    have := ae_iff.1 hS
    simpa [Set.compl_def] using this
  calc (1 : ENNReal) = P Set.univ := measure_univ.symm
    _ ≤ P (S ∪ Sᶜ) := by rw [Set.union_compl_self]
    _ ≤ P S + P Sᶜ := measure_union_le _ _
    _ = P S := by rw [h0, add_zero]

/-- The probabilistic core of the proof of Theorem 2: convergence in distribution of `Z n`
plus an a.s.-eventual inclusion gives a liminf lower bound for arbitrary (possibly
non-measurable) events. -/
theorem srpD_combine {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → Set Ω) (Z : ℕ → Ω → ℝ) (hZm : ∀ n, Measurable (Z n))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hZ : TendstoInDistribution Z atTop id (fun _ => P) ν) (c0 : ℝ)
    (hB : ∀ t > c0, ∃ B : ℕ → Set Ω, (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ B n) ∧
      ∀ n, {ω | t < Z n ω} ∩ B n ⊆ A n) :
    ν (Set.Ioi c0) ≤ liminf (fun n => P (A n)) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  have hU : Set.Ioi c0 = ⋃ k : ℕ, Set.Ioi (c0 + 1 / ((k : ℝ) + 1)) := by
    ext y; simp only [Set.mem_Ioi, Set.mem_iUnion]
    constructor
    · intro hy
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone fun k : ℕ => Set.Ioi (c0 + 1 / ((k : ℝ) + 1)) := by
    intro i j hij y hy
    simp only [Set.mem_Ioi] at hy ⊢
    have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      linarith
    linarith
  rw [hU, hmono.measure_iUnion] at hr
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hr
  set t := c0 + 1 / ((k : ℝ) + 1) with ht_def
  have ht : t > c0 := by
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  obtain ⟨B, hBae, hBsub⟩ := hB t ht
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hZ.tendsto
    (isOpen_Ioi (a := t))
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at hport
  have hEq : ∀ n, (P.map (Z n)) (Set.Ioi t) = P (Z n ⁻¹' Set.Ioi t) := fun n =>
    Measure.map_apply (hZm n) measurableSet_Ioi
  simp only [hEq] at hport
  have hr_top : r ≠ ⊤ := ne_top_of_lt (hk.trans_le prob_le_one)
  set L := (ν (Set.Ioi t)).toReal with hL
  set ρ := r.toReal with hρ
  have hρL : ρ < L := (ENNReal.toReal_lt_toReal hr_top (measure_ne_top _ _)).2 hk
  have hρ0 : 0 ≤ ρ := ENNReal.toReal_nonneg
  have hL1 : L ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ν) (s := Set.Ioi t))
    simpa using this
  set η := (L - ρ) / 3 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hLη : ENNReal.ofReal (L - η) < ν (Set.Ioi t) := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal (by linarith) (measure_ne_top _ _)]
    linarith
  have hE : ∀ᶠ n in atTop, ENNReal.ofReal (L - η) < P (Z n ⁻¹' Set.Ioi t) :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le hLη hport)
  let G : ℕ → Set Ω := fun N => {ω | ∀ m ≥ N, ω ∈ B m}
  have hGmono : Monotone G := by
    intro i j hij ω hω m hm
    exact hω m (le_trans hij hm)
  have hGun : P (⋃ N, G N) = 1 := by
    apply srpD_ae_one
    filter_upwards [hBae] with ω hω
    obtain ⟨N, hN⟩ := eventually_atTop.1 hω
    exact Set.mem_iUnion.2 ⟨N, hN⟩
  rw [hGmono.measure_iUnion] at hGun
  have h1η : ENNReal.ofReal (1 - η) < ⨆ N, P (G N) := by
    rw [hGun]; exact ENNReal.ofReal_lt_one.2 (by linarith)
  obtain ⟨N, hN⟩ := lt_iSup_iff.1 h1η
  have hgN : 1 - η < (P (G N)).toReal := by
    have := (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) (measure_ne_top _ _)).1 hN
    exact this
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hE, eventually_ge_atTop N] with n hn hnN
  have hEm : MeasurableSet (Z n ⁻¹' Set.Ioi t) := hZm n measurableSet_Ioi
  have hkey : P (G N) ≤ P (A n) + (1 - P (Z n ⁻¹' Set.Ioi t)) := by
    rw [← prob_compl_eq_one_sub hEm]
    calc P (G N) = P (G N ∩ Z n ⁻¹' Set.Ioi t) + P (G N \ Z n ⁻¹' Set.Ioi t) :=
          (measure_inter_add_sdiff _ hEm).symm
      _ ≤ P (A n) + P (Z n ⁻¹' Set.Ioi t)ᶜ := by
          gcongr
          · intro ω hω
            exact hBsub n ⟨hω.2, hω.1 n hnN⟩
          · intro ω hω; exact hω.2
  have hkeyR : (P (G N)).toReal ≤ (P (A n)).toReal + (1 - (P (Z n ⁻¹' Set.Ioi t)).toReal) := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _,
      ENNReal.sub_ne_top ENNReal.one_ne_top⟩) hkey
    rwa [ENNReal.toReal_add (measure_ne_top _ _) (ENNReal.sub_ne_top ENNReal.one_ne_top),
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one] at this
  have heR : L - η < (P (Z n ⁻¹' Set.Ioi t)).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) (measure_ne_top _ _)).1 hn
  rw [← ENNReal.ofReal_toReal hr_top, ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  linarith


theorem srpD_N1_Iio (c : ℝ) :
    gaussianReal 0 1 (Set.Iio c) = ENNReal.ofReal (cdf (gaussianReal 0 1) c) := by
  haveI := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [measure_congr Iio_ae_eq_Iic, cdf_eq_real, ofReal_measureReal]

theorem srpD_gauss {σ : ℝ} (hσ : 0 < σ) (c : ℝ) :
    gaussianReal 0 (σ ^ 2).toNNReal (Set.Ioi (-(c * σ))) =
      ENNReal.ofReal (cdf (gaussianReal 0 1) c) := by
  have hmap : gaussianReal 0 (σ ^ 2).toNNReal =
      ((gaussianReal 0 1).map (fun x => σ * x)).map (fun x => -x) := by
    rw [gaussianReal_map_const_mul, gaussianReal_map_neg]
    congr 1
    · simp
    · ext; simp [Real.toNNReal_of_nonneg (sq_nonneg σ)]
  rw [hmap, Measure.map_map measurable_neg (measurable_const_mul σ),
    Measure.map_apply (measurable_neg.comp (measurable_const_mul σ)) measurableSet_Ioi,
    ← srpD_N1_Iio]
  congr 1
  ext x
  simp only [Set.mem_preimage, Function.comp_apply, Set.mem_Ioi, Set.mem_Iio, neg_lt_neg_iff]
  rw [mul_comm c σ]
  exact mul_lt_mul_iff_right₀ hσ

theorem srpD_cdf_neg {z : ℝ} (hz : z < 0) : cdf (gaussianReal 0 1) z < 1 / 2 := by
  set N := gaussianReal 0 1
  haveI := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hsym : N (Set.Iic (-z)) = N (Set.Ioi z) := by
    have : N = N.map (fun x => -x) := by rw [gaussianReal_map_neg, neg_zero]
    rw [this, Measure.map_apply measurable_neg measurableSet_Iic, ← this]
    rw [measure_congr Ioi_ae_eq_Ici]
    congr 1
    ext x; simp [neg_le]
  have hsplit : N (Set.Iic (-z)) = N (Set.Iic z) + N (Set.Ioc z (-z)) := by
    rw [← measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic (by linarith)]
  have htot : N (Set.Iic z) + N (Set.Ioi z) = 1 := by
    rw [← Set.compl_Iic, measure_add_measure_compl measurableSet_Iic, measure_univ]
  have hpos : 0 < N (Set.Ioc z (-z)) := by
    have hac := gaussianReal_absolutelyContinuous' 0 (v := 1) one_ne_zero
    refine lt_of_lt_of_le ?_ (measure_mono (Set.Ioo_subset_Ioc_self))
    rw [pos_iff_ne_zero]
    intro h0
    have := hac h0
    rw [Real.volume_Ioo] at this
    simp only [ENNReal.ofReal_eq_zero] at this
    linarith
  rw [cdf_eq_real]
  have e : N (Set.Iic z) + N (Set.Iic z) + N (Set.Ioc z (-z)) = 1 := by
    rw [add_assoc, ← hsplit, hsym, htot]
  have e' := congrArg ENNReal.toReal e
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness)
    (by finiteness), ENNReal.toReal_one] at e'
  have hq : 0 < (N (Set.Ioc z (-z))).toReal := ENNReal.toReal_pos hpos.ne' (by finiteness)
  show (N (Set.Iic z)).toReal < 1 / 2
  linarith

theorem srpD_sqrt_lo {u : ℕ → ℝ} {v : ℝ} (h : ∀ ε > 0, ∀ᶠ n in atTop, v - ε ≤ u n)
    (β : ℝ) (hβ : β < Real.sqrt v) : ∀ᶠ n in atTop, β ≤ Real.sqrt (u n) := by
  by_cases hβ0 : β ≤ 0
  · exact Eventually.of_forall fun n => hβ0.trans (Real.sqrt_nonneg _)
  push_neg at hβ0
  have hβv : β ^ 2 < v := (Real.lt_sqrt hβ0.le).1 hβ
  filter_upwards [h (v - β ^ 2) (by linarith)] with n hn
  exact Real.le_sqrt_of_sq_le (by linarith)

theorem srpD_sqrt_hi {u : ℕ → ℝ} {v : ℝ} (h : ∀ ε > 0, ∀ᶠ n in atTop, u n ≤ v + ε)
    (β : ℝ) (hβ : Real.sqrt v < β) : ∀ᶠ n in atTop, Real.sqrt (u n) ≤ β := by
  have hβ0 : 0 < β := lt_of_le_of_lt (Real.sqrt_nonneg _) hβ
  have hβv : v < β ^ 2 := (Real.sqrt_lt' hβ0).1 hβ
  filter_upwards [h (β ^ 2 - v) (by linarith)] with n hn
  rw [Real.sqrt_le_left hβ0.le]
  linarith

/-- Deterministic core of (7)–(8): the gap event contains the CLT event. -/
theorem srpD_incl {d : ℕ} {Ξ : Type*} (f : E d → Ξ → ℝ) (X : Set (E d)) (xhat xs : E d)
    (hxs : xs ∈ X) (s : ℕ → Ξ) (n : ℕ) (z : E d)
    (hmin : z ∈ X ∧ ∀ y ∈ X, sampleMean f s n z ≤ sampleMean f s n y) (hn : 1 ≤ n)
    (m zα r : ℝ)
    (h : -zα * r * Real.sqrt n ≤
      ∑ k ∈ Finset.range n, (f xhat (s k) - f xs (s k)) - n * m) :
    m ≤ gapEstimate f X xhat s n + zα * r / Real.sqrt n := by
  have hsaa : saaValue f X s n ≤ sampleMean f s n xs := by
    unfold saaValue
    refine csInf_le ⟨sampleMean f s n z, ?_⟩ ⟨xs, hxs, rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmin.2 y hy
  have hdiff : sampleMean f s n xhat - sampleMean f s n xs =
      (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, (f xhat (s k) - f xs (s k)) := by
    unfold sampleMean; rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hnq : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
  set S := ∑ k ∈ Finset.range n, (f xhat (s k) - f xs (s k))
  set q := Real.sqrt n
  have key : (1 / (n : ℝ)) * S + zα * r / q - m = (S - n * m + zα * r * q) / n := by
    rw [hnq]; field_simp; ring
  have hnn : (0 : ℝ) < n := by exact_mod_cast hn
  have : 0 ≤ (S - n * m + zα * r * q) / n := div_nonneg (by linarith) hnn.le
  unfold gapEstimate
  linarith

end SolutionQuality.SRP


namespace SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter Topology

/-- Data for the CLT step at an optimal point `xs`. -/
theorem srpE_setup {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (xhat : E d) (hxhat : xhat ∈ X) (xs : E d) (hxs : xs ∈ optSet μ f X) :
    MemLp (fun ω => f xhat (ξ 0 ω) - f xs (ξ 0 ω)) 2 P ∧
    iIndepFun (fun k ω => f xhat (ξ k ω) - f xs (ξ k ω)) P ∧
    (∀ i, IdentDistrib (fun ω => f xhat (ξ i ω) - f xs (ξ i ω))
      (fun ω => f xhat (ξ 0 ω) - f xs (ξ 0 ω)) P P) ∧
    Var[fun ω => f xhat (ξ 0 ω) - f xs (ξ 0 ω); P] = gapVar μ f xhat xs ∧
    P[fun ω => f xhat (ξ 0 ω) - f xs (ξ 0 ω)] = optGap μ f X xhat ∧
    (∀ k, Measurable (fun ω => f xhat (ξ k ω) - f xs (ξ k ω))) ∧
    MemLp (fun s => f xhat s - f xs s) 2 μ := by
  obtain ⟨g, hg, hg0, hgb⟩ := srpB_env μ f X hA
  set h : Ξ → ℝ := fun s => f xhat s - f xs s with hh
  have hhm : Measurable h := (hfm xhat).sub (hfm xs)
  have hint : ∀ x ∈ X, Integrable (f x) μ := by
    intro x hx
    refine Integrable.mono' ((integrable_const 1).add hg) (hfm x).aestronglyMeasurable ?_
    filter_upwards [hgb] with s hs
    rw [Real.norm_eq_abs]
    exact srpB_abs_le (hs x hx)
  have hmemh : MemLp h 2 μ := by
    refine (memLp_two_iff_integrable_sq hhm.aestronglyMeasurable).2 ?_
    refine Integrable.mono' (hg.const_mul 4) (hhm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hgb] with s hs
    have h1 := hs xhat hxhat
    have h2 := hs xs hxs.1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [hh]
    nlinarith [sq_nonneg (f xhat s + f xs s)]
  have hξm := hξ.1
  have hWm : ∀ k, Measurable (fun ω => f xhat (ξ k ω) - f xs (ξ k ω)) :=
    fun k => hhm.comp (hξm k)
  have hWid : ∀ k, IdentDistrib (fun ω => f xhat (ξ k ω) - f xs (ξ k ω)) h P μ := by
    intro k
    refine ⟨(hWm k).aemeasurable, hhm.aemeasurable, ?_⟩
    show P.map (h ∘ ξ k) = μ.map h
    rw [← Measure.map_map hhm (hξm k), hξ.2.2 k]
  have hWid0 := hWid 0
  refine ⟨hWid0.memLp_iff.2 hmemh, ?_, fun i => (hWid i).trans hWid0.symm,
    hWid0.variance_eq, ?_, hWm, hmemh⟩
  · exact hξ.2.1.comp (fun _ => h) (fun _ => hhm)
  · rw [hWid0.integral_eq]
    simp only [hh]
    rw [integral_sub (hint xhat hxhat) (hint xs hxs.1)]
    unfold optGap optValue
    have : sInf (expectedCost μ f '' X) = expectedCost μ f xs := by
      refine IsLeast.csInf_eq ⟨Set.mem_image_of_mem _ hxs.1, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact hxs.2 y hy
    rw [this]; rfl

/-- The CLT + Slutsky-type step (9) of the proof of Theorem 2. -/
theorem srpE_engine {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (xhat : E d) (hxhat : xhat ∈ X)
    (xn : ℕ → Ω → E d) (hxn : IsSAAMinimizerSeq P f X ξ xn)
    (zα : ℝ) (xs : E d) (hxs : xs ∈ optSet μ f X) (hσ : 0 < gapVar μ f xhat xs) (c : ℝ)
    (hB : ∀ t > -(c * Real.sqrt (gapVar μ f xhat xs)), ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      -zα * Real.sqrt (sampleVar f xhat (fun i => ξ i ω) n (xn n ω)) ≤ t) :
    ENNReal.ofReal (cdf (gaussianReal 0 1) c) ≤
      liminf (fun n : ℕ => P {ω | optGap μ f X xhat ≤
        gapEstimate f X xhat (fun i => ξ i ω) n +
          zα * Real.sqrt (sampleVar f xhat (fun i => ξ i ω) n (xn n ω)) / Real.sqrt n}) atTop := by
  obtain ⟨hmem0, hindep, hident, hvar, hmean, hWm, -⟩ :=
    srpE_setup μ f hfm X hA P ξ hξ xhat hxhat xs hxs
  set W : ℕ → Ω → ℝ := fun k ω => f xhat (ξ k ω) - f xs (ξ k ω) with hW
  set σ := Real.sqrt (gapVar μ f xhat xs) with hσdef
  have hσpos : 0 < σ := Real.sqrt_pos.2 hσ
  set ν := gaussianReal 0 (Var[W 0; P]).toNNReal with hν
  have hY : HasLaw (id : ℝ → ℝ) (gaussianReal 0 (Var[W 0; P]).toNNReal) ν :=
    ⟨aemeasurable_id, Measure.map_id⟩
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub hY hmem0 hindep hident
  set Z : ℕ → Ω → ℝ := fun n ω => (Real.sqrt n)⁻¹ * (∑ k ∈ Finset.range n, W k ω - n * P[W 0])
    with hZ
  have hZm : ∀ n, Measurable (Z n) := by
    intro n
    exact ((Finset.measurable_sum _ fun k _ => hWm k).sub measurable_const).const_mul _
  have hcomb := srpD_combine P (fun n : ℕ => {ω | optGap μ f X xhat ≤
        gapEstimate f X xhat (fun i => ξ i ω) n +
          zα * Real.sqrt (sampleVar f xhat (fun i => ξ i ω) n (xn n ω)) / Real.sqrt n})
    Z hZm ν hclt (-(c * σ)) ?_
  · have hνeq : ν = gaussianReal 0 (σ ^ 2).toNNReal := by
      rw [hν, hvar, hσdef, Real.sq_sqrt hσ.le]
    rw [hνeq, srpD_gauss hσpos] at hcomb
    exact hcomb
  · intro t ht
    refine ⟨fun n => {ω | (∀ m, xn m ω ∈ X ∧ ∀ y ∈ X,
        sampleMean f (fun i => ξ i ω) m (xn m ω) ≤ sampleMean f (fun i => ξ i ω) m y) ∧
        -zα * Real.sqrt (sampleVar f xhat (fun i => ξ i ω) n (xn n ω)) ≤ t ∧ 1 ≤ n}, ?_, ?_⟩
    · filter_upwards [ae_all_iff.2 hxn.2, hB t ht] with ω h1 h2
      filter_upwards [h2, eventually_ge_atTop 1] with n hn hn1
      exact ⟨h1, hn, hn1⟩
    · intro n ω ⟨hZω, h1, h2, h3⟩
      simp only [Set.mem_ofPred_eq] at hZω ⊢
      rw [← hmean]
      apply srpD_incl f X xhat xs hxs.1 (fun i => ξ i ω) n (xn n ω) (h1 n) h3
      have hq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast h3)
      have h4 : -zα * Real.sqrt (sampleVar f xhat (fun i => ξ i ω) n (xn n ω)) <
          (Real.sqrt n)⁻¹ * (∑ k ∈ Finset.range n, W k ω - n * P[W 0]) := lt_of_le_of_lt h2 hZω
      rw [lt_inv_mul_iff₀ hq] at h4
      simp only [hW] at h4
      linarith

/-- Degenerate case `σ²_x̂(xs) = 0`, `zα ≥ 0`: the event holds a.s. for `n ≥ 1`. -/
theorem srpE_degenerate {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (xhat : E d) (hxhat : xhat ∈ X)
    (xn : ℕ → Ω → E d) (hxn : IsSAAMinimizerSeq P f X ξ xn)
    (zα : ℝ) (hz : 0 ≤ zα) (xs : E d) (hxs : xs ∈ optSet μ f X)
    (hσ : gapVar μ f xhat xs = 0) (n : ℕ) (hn : 1 ≤ n) :
    P {ω | optGap μ f X xhat ≤
        gapEstimate f X xhat (fun i => ξ i ω) n +
          zα * Real.sqrt (sampleVar f xhat (fun i => ξ i ω) n (xn n ω)) / Real.sqrt n} = 1 := by
  obtain ⟨-, -, -, -, hmean, -, hmemh⟩ := srpE_setup μ f hfm X hA P ξ hξ xhat hxhat xs hxs
  have hconst := ae_eq_integral_of_variance_eq_zero hmemh hσ
  have hW : ∀ᵐ ω ∂P, ∀ k, f xhat (ξ k ω) - f xs (ξ k ω) =
      ∫ s, (f xhat s - f xs s) ∂μ := by
    refine ae_all_iff.2 fun k => ?_
    have h1 : ∀ᵐ y ∂(P.map (ξ k)), f xhat y - f xs y = ∫ s, (f xhat s - f xs s) ∂μ := by
      rw [hξ.2.2 k]; exact hconst
    exact ae_of_ae_map (hξ.1 k).aemeasurable h1
  have hmean' : ∫ s, (f xhat s - f xs s) ∂μ = optGap μ f X xhat := by
    rw [← hmean]
    have hid : IdentDistrib (fun ω => f xhat (ξ 0 ω) - f xs (ξ 0 ω))
        (fun s => f xhat s - f xs s) P μ := by
      refine ⟨(((hfm xhat).sub (hfm xs)).comp (hξ.1 0)).aemeasurable,
        ((hfm xhat).sub (hfm xs)).aemeasurable, ?_⟩
      show P.map ((fun s => f xhat s - f xs s) ∘ ξ 0) = _
      rw [← Measure.map_map (show Measurable (fun s => f xhat s - f xs s) from
        (hfm xhat).sub (hfm xs)) (hξ.1 0), hξ.2.2 0]
    exact hid.integral_eq.symm
  apply srpD_ae_one
  filter_upwards [hW, ae_all_iff.2 hxn.2] with ω hω hmin
  show optGap μ f X xhat ≤ _
  apply srpD_incl f X xhat xs hxs.1 (fun i => ξ i ω) n (xn n ω) (hmin n) hn
  have hS : ∑ k ∈ Finset.range n, (f xhat (ξ k ω) - f xs (ξ k ω)) =
      n * optGap μ f X xhat := by
    rw [Finset.sum_congr rfl fun k _ => hω k, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, hmean']
  rw [hS, sub_self]
  have : 0 ≤ zα * Real.sqrt (sampleVar f xhat (fun i => ξ i ω) n (xn n ω)) * Real.sqrt n :=
    mul_nonneg (mul_nonneg hz (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  linarith

/-- Existence of `x*_min`, `x*_max` (minimizers/maximizers of `σ²_x̂` over the compact `X*`). -/
theorem srpE_minmax {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X) (xhat : E d) (hxhat : xhat ∈ X) :
    ∃ xmin xmax : E d,
      (xmin ∈ optSet μ f X ∧ ∀ x ∈ optSet μ f X, gapVar μ f xhat xmin ≤ gapVar μ f xhat x) ∧
      (xmax ∈ optSet μ f X ∧ ∀ x ∈ optSet μ f X, gapVar μ f xhat x ≤ gapVar μ f xhat xmax) := by
  haveI : CompactSpace X := isCompact_iff_compactSpace.mp hA.A3.2
  -- any i.i.d. sample is not needed for the deterministic limits; use the product space
  let P : Measure (ℕ → Ξ) := Measure.infinitePi (fun _ => μ)
  have hξ : IsIIDSample P μ (fun i ω => ω i) := by
    refine ⟨fun i => measurable_pi_apply i, ?_, fun i => ?_⟩
    · exact iIndepFun_infinitePi (P := fun _ => μ) (X := fun _ x => x) (fun _ => measurable_id)
    · simpa using (measurePreserving_eval_infinitePi (fun _ => μ) i).map_eq
  obtain ⟨a, ha, -⟩ := srpB_fbar_C μ f hfm X hA P _ hξ
  have hEf := srpC_contOn_of_C a _ ha
  obtain ⟨v, hv, -⟩ := srpB_var_C μ f hfm X hA P _ hξ xhat hxhat
  have hvc := srpC_contOn_of_C v _ hv
  obtain ⟨x0, hx0X, hx0⟩ := hA.A3.2.exists_isMinOn hA.A3.1 hEf
  have hopt : optSet μ f X = X ∩ expectedCost μ f ⁻¹' Set.Iic (expectedCost μ f x0) := by
    ext x
    simp only [optSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨hx, hle⟩; exact ⟨hx, hle x0 hx0X⟩
    · rintro ⟨hx, hle⟩; exact ⟨hx, fun y hy => hle.trans (hx0 hy)⟩
  have hcl : IsClosed (optSet μ f X) := by
    rw [hopt]; exact hEf.preimage_isClosed_of_isClosed hA.A3.2.isClosed isClosed_Iic
  have hcpt : IsCompact (optSet μ f X) :=
    hA.A3.2.of_isClosed_subset hcl (fun x hx => hx.1)
  have hne : (optSet μ f X).Nonempty := ⟨x0, hx0X, fun y hy => hx0 hy⟩
  have hvc' : ContinuousOn (gapVar μ f xhat) (optSet μ f X) := hvc.mono fun x hx => hx.1
  obtain ⟨xmin, hxmin, hmin⟩ := hcpt.exists_isMinOn hne hvc'
  obtain ⟨xmax, hxmax, hmax⟩ := hcpt.exists_isMaxOn hne hvc'
  exact ⟨xmin, xmax, ⟨hxmin, fun x hx => hmin hx⟩, ⟨hxmax, fun x hx => hmax hx⟩⟩

end SolutionQuality.SRP


namespace SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter Topology

theorem srpF_zα_nonneg {α zα : ℝ} (hzα : cdf (gaussianReal 0 1) zα = 1 - α)
    (hα : α ≤ 1 / 2) : 0 ≤ zα := by
  by_contra h
  have := srpD_cdf_neg (lt_of_not_ge h)
  rw [hzα] at this
  linarith

theorem srpF_main {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (xhat : E d) (hxhat : xhat ∈ X)
    (xn : ℕ → Ω → E d) (hxn : IsSAAMinimizerSeq P f X ξ xn)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (zα : ℝ) (hzα : cdf (gaussianReal 0 1) zα = 1 - α)
    (hdeg : α ≤ 1 / 2 ∨ ∃ x ∈ optSet μ f X, 0 < gapVar μ f xhat x)
    (hiii : ∀ xmin xmax : E d,
      (xmin ∈ optSet μ f X ∧ ∀ x ∈ optSet μ f X, gapVar μ f xhat xmin ≤ gapVar μ f xhat x) →
      (xmax ∈ optSet μ f X ∧ ∀ x ∈ optSet μ f X, gapVar μ f xhat x ≤ gapVar μ f xhat xmax) →
      ∀ᵐ ω ∂P, ∀ ε > 0, ∀ᶠ n in atTop,
        gapVar μ f xhat xmin - ε ≤ sampleVar f xhat (fun i => ξ i ω) n (xn n ω) ∧
          sampleVar f xhat (fun i => ξ i ω) n (xn n ω) ≤ gapVar μ f xhat xmax + ε) :
    ENNReal.ofReal (1 - α) ≤
      liminf (fun n : ℕ => P {ω | optGap μ f X xhat ≤
        gapEstimate f X xhat (fun i => ξ i ω) n +
          zα * Real.sqrt (sampleVar f xhat (fun i => ξ i ω) n (xn n ω)) / Real.sqrt n}) atTop := by
  obtain ⟨xmin, xmax, hxmin, hxmax⟩ := srpE_minmax μ f hfm X hA xhat hxhat
  have h3 := hiii xmin xmax hxmin hxmax
  have hrhs : ENNReal.ofReal (1 - α) = ENNReal.ofReal (cdf (gaussianReal 0 1) zα) := by
    rw [hzα]
  by_cases hz : 0 ≤ zα
  · by_cases hσ0 : gapVar μ f xhat xmin = 0
    · refine le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [srpE_degenerate μ f hfm X hA P ξ hξ xhat hxhat xn hxn zα hz xmin hxmin.1 hσ0 n hn]
      exact ENNReal.ofReal_le_one.2 (by linarith)
    · have hσ : 0 < gapVar μ f xhat xmin :=
        lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hσ0)
      rw [hrhs]
      apply srpE_engine μ f hfm X hA P ξ hξ xhat hxhat xn hxn zα xmin hxmin.1 hσ zα
      intro t ht
      filter_upwards [h3] with ω hω
      have hlo : ∀ ε > 0, ∀ᶠ n in atTop, gapVar μ f xhat xmin - ε ≤
          sampleVar f xhat (fun i => ξ i ω) n (xn n ω) :=
        fun ε hε => (hω ε hε).mono fun n hn => hn.1
      rcases hz.lt_or_eq with hzpos | hz0
      · have hβ : -t / zα < Real.sqrt (gapVar μ f xhat xmin) := by
          rw [div_lt_iff₀ hzpos]; linarith
        filter_upwards [srpD_sqrt_lo hlo _ hβ] with n hn
        have h1 := mul_le_mul_of_nonneg_left hn hzpos.le
        rw [mul_div_cancel₀ _ hzpos.ne'] at h1
        linarith
      · subst hz0
        refine Eventually.of_forall fun n => ?_
        simp only [neg_zero, zero_mul] at ht ⊢
        linarith
  · have hzneg : zα < 0 := lt_of_not_ge hz
    have hσmax : 0 < gapVar μ f xhat xmax := by
      rcases hdeg with hα | ⟨x, hx, hxpos⟩
      · exact absurd (srpF_zα_nonneg hzα hα) hz
      · exact lt_of_lt_of_le hxpos (hxmax.2 x hx)
    rw [hrhs]
    apply srpE_engine μ f hfm X hA P ξ hξ xhat hxhat xn hxn zα xmax hxmax.1 hσmax zα
    intro t ht
    filter_upwards [h3] with ω hω
    have hhi : ∀ ε > 0, ∀ᶠ n in atTop, sampleVar f xhat (fun i => ξ i ω) n (xn n ω) ≤
        gapVar μ f xhat xmax + ε :=
      fun ε hε => (hω ε hε).mono fun n hn => hn.2
    have hnz : 0 < -zα := neg_pos.2 hzneg
    have hβ : Real.sqrt (gapVar μ f xhat xmax) < t / (-zα) := by
      rw [lt_div_iff₀ hnz]; linarith
    filter_upwards [srpD_sqrt_hi hhi _ hβ] with n hn
    have h1 := mul_le_mul_of_nonneg_left hn hnz.le
    rw [mul_div_cancel₀ _ hnz.ne'] at h1
    linarith

end SolutionQuality.SRP


namespace SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter Topology

theorem srpF_eps_bound {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (xhat : E d) (hxhat : xhat ∈ X)
    (xn : ℕ → Ω → E d) (hxn : IsSAAMinimizerSeq P f X ξ xn)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (zα : ℝ) (hzα : cdf (gaussianReal 0 1) zα = 1 - α)
    (xmin : E d)
    (hxmin : xmin ∈ optSet μ f X ∧ ∀ x ∈ optSet μ f X, gapVar μ f xhat xmin ≤ gapVar μ f xhat x)
    (hσ : 0 < gapVar μ f xhat xmin) (hαhalf : α ≤ 1 / 2)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ENNReal.ofReal (cdf (gaussianReal 0 1) ((1 - ε) * zα)) ≤
      liminf (fun n : ℕ => P {ω | optGap μ f X xhat ≤
        gapEstimate f X xhat (fun i => ξ i ω) n +
          zα * Real.sqrt (sampleVar f xhat (fun i => ξ i ω) n (xn n ω)) / Real.sqrt n}) atTop := by
  obtain ⟨-, xmax, -, hxmax⟩ := srpE_minmax μ f hfm X hA xhat hxhat
  have h3 := srpC_prop1_iii μ f hfm X hA P ξ hξ xhat hxhat xn hxn xmin xmax hxmin hxmax
  have hz := srpF_zα_nonneg hzα hαhalf
  apply srpE_engine μ f hfm X hA P ξ hξ xhat hxhat xn hxn zα xmin hxmin.1 hσ ((1 - ε) * zα)
  intro t ht
  filter_upwards [h3] with ω hω
  have hlo : ∀ ε > 0, ∀ᶠ n in atTop, gapVar μ f xhat xmin - ε ≤
      sampleVar f xhat (fun i => ξ i ω) n (xn n ω) :=
    fun ε hε => (hω ε hε).mono fun n hn => hn.1
  rcases hz.lt_or_eq with hzpos | hz0
  · have hs := Real.sqrt_nonneg (gapVar μ f xhat xmin)
    have hle : (1 - ε) * zα * Real.sqrt (gapVar μ f xhat xmin) ≤
        zα * Real.sqrt (gapVar μ f xhat xmin) := by
      nlinarith [mul_nonneg hzpos.le hs]
    have hβ : -t / zα < Real.sqrt (gapVar μ f xhat xmin) := by
      rw [div_lt_iff₀ hzpos]; linarith
    filter_upwards [srpD_sqrt_lo hlo _ hβ] with n hn
    have h1 := mul_le_mul_of_nonneg_left hn hzpos.le
    rw [mul_div_cancel₀ _ hzpos.ne'] at h1
    linarith
  · subst hz0
    refine Eventually.of_forall fun n => ?_
    simp only [mul_zero, neg_zero, zero_mul] at ht ⊢
    linarith

end SolutionQuality.SRP

open MeasureTheory ProbabilityTheory Filter SolutionQuality.SRP

theorem solution {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (hfm : ∀ x, Measurable (f x))
    (X : Set (E d)) (hA : Assumptions μ f X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (xhat : E d) (hxhat : xhat ∈ X)
    (xn : ℕ → Ω → E d) (hxn : IsSAAMinimizerSeq P f X ξ xn)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (zα : ℝ) (hzα : cdf (gaussianReal 0 1) zα = 1 - α)
    (xmin : E d)
    (hxmin : xmin ∈ optSet μ f X ∧ ∀ x ∈ optSet μ f X, gapVar μ f xhat xmin ≤ gapVar μ f xhat x)
    (hσ : 0 < gapVar μ f xhat xmin) (hαhalf : α ≤ 1 / 2)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ENNReal.ofReal (cdf (gaussianReal 0 1) ((1 - ε) * zα)) ≤
      liminf (fun n : ℕ => P {ω | optGap μ f X xhat ≤
        gapEstimate f X xhat (fun i => ξ i ω) n +
          zα * Real.sqrt (sampleVar f xhat (fun i => ξ i ω) n (xn n ω)) / Real.sqrt n}) atTop :=
  srpF_eps_bound μ f hfm X hA P ξ hξ xhat hxhat xn hxn α hα0 hα1 zα hzα xmin hxmin hσ hαhalf
    ε hε0 hε1
