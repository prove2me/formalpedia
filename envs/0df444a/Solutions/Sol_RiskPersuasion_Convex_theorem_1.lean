-- Prove2me | solution 1 for RiskPersuasion.Convex.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T05:47:49.797264+00:00
-- url     : https://prove2.me/submissions/ad15d324-0225-493b-b2f9-b549eef44146

import Mathlib
import Definitions.Def_RiskPersuasion_Convex_Program7

set_option autoImplicit false

open MeasureTheory

namespace RPConvexAux

open RiskPersuasion.Convex

/-- In finite dimensions the convex hull of a compact set is compact (Caratheodory). -/
lemma hull_compact {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) : IsCompact (convexHull ℝ K) := by
  have key : convexHull ℝ K = ⋃ k ∈ Finset.range (Module.finrank ℝ E + 2),
      (fun p : (Fin k → ℝ) × (Fin k → E) => ∑ i, p.1 i • p.2 i) ''
        (stdSimplex ℝ (Fin k) ×ˢ Set.univ.pi (fun _ => K)) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_range, Set.mem_prod, Set.mem_pi,
      Set.mem_univ, true_implies, Prod.exists, exists_prop]
    constructor
    · intro hx
      obtain ⟨ι, _, z, w, hzK, hai, hw0, hw1, hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
      have hc := hai.card_le_finrank_succ
      have hc2 := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
      let e := Fintype.equivFin ι
      refine ⟨Fintype.card ι, by omega, w ∘ e.symm, z ∘ e.symm,
        ⟨⟨fun i => (hw0 _).le, ?_⟩, fun i => hzK ⟨_, rfl⟩⟩, ?_⟩
      · rw [← hw1]; exact e.symm.sum_comp w
      · rw [← hx]; exact e.symm.sum_comp (fun i => w i • z i)
    · rintro ⟨k, -, w, z, ⟨⟨hw0, hw1⟩, hz⟩, rfl⟩
      exact (convex_convexHull ℝ K).sum_mem (fun i _ => hw0 i) hw1
        (fun i _ => subset_convexHull ℝ K (hz i))
  rw [key]
  refine (Finset.range _).isCompact_biUnion fun k _ => ?_
  exact ((isCompact_stdSimplex ℝ (Fin k)).prod (isCompact_univ_pi fun _ => hK)).image
    (by fun_prop)

lemma simplex_norm_le {Ω : Type} [Fintype Ω] {x : Ω → ℝ} (hx : x ∈ stdSimplex ℝ Ω) :
    ‖x‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (hx.1 ω), ← hx.2]
  exact Finset.single_le_sum (fun i _ => hx.1 i) (Finset.mem_univ ω)

lemma subset_dir {Ω A : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype A] (μstar : Ω → ℝ) (hμ : μstar ∈ stdSimplex ℝ Ω) (ρ : (Ω → ℝ) → A → ℝ)
    (v : Ω → A → ℝ) (hP : ∀ a : A, IsClosed (P ρ a)) :
    achievableValues μstar ρ v ⊆ objective7 v '' {t | Feasible7 μstar ρ t} := by
  rintro x ⟨S, mS, π, post, act, ⟨⟨hprob, hmarg⟩, ⟨hpS, hpm, hpi⟩, hopt, hmeas⟩, rfl⟩
  have : IsProbabilityMeasure (π.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hpostm : Measurable post := measurable_pi_iff.2 hpm
  have hint : Integrable post (π.map Prod.snd) :=
    Integrable.of_bound hpostm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun s => simplex_norm_le (hpS s))
  have hBm : ∀ b, MeasurableSet (act ⁻¹' {b}) := hmeas
  have hSm : ∀ (ω : Ω) (b : A), MeasurableSet ({ω} ×ˢ (act ⁻¹' {b})) :=
    fun ω b => (measurableSet_singleton ω).prod (hBm b)
  refine ⟨fun b ω => (π ({ω} ×ˢ (act ⁻¹' {b}))).toReal, ⟨?_, ?_⟩, ?_⟩
  · intro ω
    have hU : ({ω} ×ˢ (Set.univ : Set S)) =
        ⋃ b ∈ (Finset.univ : Finset A), {ω} ×ˢ (act ⁻¹' {b}) := by
      ext p; simp [Set.mem_prod]
    have h1 : π ({ω} ×ˢ (Set.univ : Set S)) = ∑ b, π ({ω} ×ˢ (act ⁻¹' {b})) := by
      rw [hU]
      refine measure_biUnion_finset ?_ (fun b _ => hSm ω b)
      intro b _ c _ hbc
      refine Set.disjoint_left.2 fun p hp hq => hbc ?_
      exact (Set.mem_singleton_iff.mp hp.2).symm.trans (Set.mem_singleton_iff.mp hq.2)
    calc ∑ b, (π ({ω} ×ˢ (act ⁻¹' {b}))).toReal
        = (∑ b, π ({ω} ×ˢ (act ⁻¹' {b}))).toReal :=
          (ENNReal.toReal_sum fun b _ => measure_ne_top π _).symm
      _ = μstar ω := by rw [← h1, hmarg ω, ENNReal.toReal_ofReal (hμ.1 ω)]
  · intro b
    show (fun ω => (π ({ω} ×ˢ (act ⁻¹' {b}))).toReal) ∈ convexHull ℝ (P ρ b ∪ {0})
    have hintB : Integrable post ((π.map Prod.snd).restrict (act ⁻¹' {b})) := hint.integrableOn
    have ht : (fun ω => (π ({ω} ×ˢ (act ⁻¹' {b}))).toReal) =
        ∫ s in act ⁻¹' {b}, post s ∂(π.map Prod.snd) := by
      funext ω
      rw [eval_integral (fun i => hintB.eval i) ω]
      exact hpi ω _ (hBm b)
    rcases eq_or_ne ((π.map Prod.snd) (act ⁻¹' {b})) 0 with h0 | h0
    · rw [ht, setIntegral_measure_zero _ h0]
      exact subset_convexHull ℝ _ (Set.mem_union_right _ rfl)
    · have hK : IsCompact (P ρ b) :=
        (isCompact_stdSimplex ℝ Ω).of_isClosed_subset (hP b) (fun x hx => hx.1)
      have havg := (convex_convexHull ℝ (P ρ b)).set_average_mem (hull_compact hK).isClosed h0
        (measure_ne_top _ _) (by
          rw [ae_restrict_iff' (hBm b)]
          refine Filter.Eventually.of_forall fun s hs => subset_convexHull ℝ _ ?_
          have := hopt s
          rwa [Set.mem_singleton_iff.mp hs] at this) hint.integrableOn
      rw [setAverage_eq] at havg
      set m := (π.map Prod.snd).real (act ⁻¹' {b}) with hm
      have hm0 : 0 < m := by
        rw [hm, measureReal_def]; exact ENNReal.toReal_pos h0 (measure_ne_top _ _)
      have hm1 : m ≤ 1 := by
        rw [hm]; exact measureReal_le_one
      have heq : (fun ω => (π ({ω} ×ˢ (act ⁻¹' {b}))).toReal) =
          m • (m⁻¹ • ∫ s in act ⁻¹' {b}, post s ∂(π.map Prod.snd)) + (1 - m) • (0 : Ω → ℝ) := by
        rw [smul_zero, add_zero, smul_smul, mul_inv_cancel₀ hm0.ne', one_smul, ht]
      rw [heq]
      exact convex_convexHull ℝ (P ρ b ∪ {0}) (convexHull_mono Set.subset_union_left havg)
        (subset_convexHull ℝ _ (Set.mem_union_right _ (Set.mem_singleton (0 : Ω → ℝ)))) hm0.le (by linarith : (0:ℝ) ≤ 1 - m) (by ring : m + (1 - m) = 1)
  · show objective7 v _ = senderValue v π act
    unfold objective7 senderValue
    have hpt : (fun p : Ω × S => v p.1 (act p.2)) = fun p => ∑ ω, ∑ b,
        ({ω} ×ˢ (act ⁻¹' {b})).indicator (fun _ => v ω b) p := by
      funext p
      symm
      rw [Finset.sum_eq_single p.1, Finset.sum_eq_single (act p.2)]
      · simp [Set.mem_prod]
      · intro b _ hb
        simp [Set.mem_prod, Ne.symm hb]
      · simp
      · intro ω _ hω
        refine Finset.sum_eq_zero fun b _ => ?_
        simp [Set.mem_prod, Ne.symm hω]
      · simp
    rw [hpt, integral_finsetSum _ (fun ω _ => integrable_finsetSum _ fun b _ =>
      (integrable_const _).indicator (hSm ω b))]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [integral_finsetSum _ (fun b _ => (integrable_const _).indicator (hSm ω b))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_indicator_const _ (hSm ω b), smul_eq_mul, measureReal_def]

lemma supset_dir {Ω A : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype A] [Nonempty A] (μstar : Ω → ℝ) (hμ : μstar ∈ stdSimplex ℝ Ω)
    (ρ : (Ω → ℝ) → A → ℝ) (v : Ω → A → ℝ) :
    objective7 v '' {t | Feasible7 μstar ρ t} ⊆ achievableValues μstar ρ v := by
  classical
  rintro x ⟨t, ⟨hsum, hhull⟩, rfl⟩
  have hdec : ∀ b, ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (z : ι → Ω → ℝ), (∀ i, 0 ≤ w i) ∧
      ∑ i, w i = 1 ∧ (∀ i, z i ∈ P ρ b ∪ {0}) ∧ ∑ i, w i • z i = t b :=
    fun b => mem_convexHull_iff_exists_fintype.1 (hhull b)
  choose ι hι w z hw0 hw1 hz hwz using hdec
  obtain ⟨a0, -, ha0⟩ := Finset.exists_max_image Finset.univ (ρ μstar) Finset.univ_nonempty
  have hμP : μstar ∈ P ρ a0 := ⟨hμ, fun a' => ha0 a' (Finset.mem_univ _)⟩
  letI : ∀ b, Fintype (ι b) := hι
  let S : Type := Σ b : A, ι b
  letI mS : MeasurableSpace S := ⊤
  haveI : MeasurableSingletonClass S := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hz0 : ∀ s : S, z s.1 s.2 ∉ P ρ s.1 → z s.1 s.2 = 0 := fun s h =>
    Set.mem_singleton_iff.mp ((hz s.1 s.2).resolve_left h)
  have hzn : ∀ (s : S) (ω : Ω), 0 ≤ z s.1 s.2 ω := by
    intro s ω
    by_cases h : z s.1 s.2 ∈ P ρ s.1
    · exact h.1.1 ω
    · rw [hz0 s h]; exact le_refl _
  let post : S → Ω → ℝ := fun s => if z s.1 s.2 ∈ P ρ s.1 then z s.1 s.2 else μstar
  let act : S → A := fun s => if z s.1 s.2 ∈ P ρ s.1 then s.1 else a0
  let q : Ω × S → ℝ := fun p => w p.2.1 p.2.2 * z p.2.1 p.2.2 p.1
  have hq0 : ∀ p, 0 ≤ q p := fun p => mul_nonneg (hw0 _ _) (hzn _ _)
  have htb : ∀ b ω, ∑ i, w b i * z b i ω = t b ω := by
    intro b ω; rw [← hwz b]; simp [Finset.sum_apply]
  have hrow : ∀ ω, ∑ s : S, q (ω, s) = μstar ω := by
    intro ω; rw [Fintype.sum_sigma]; simp only [q]; simp_rw [htb]; exact hsum ω
  have hqz : ∀ (s : S) (ω : Ω), q (ω, s) = (∑ ω', q (ω', s)) * post s ω := by
    intro s ω
    by_cases h : z s.1 s.2 ∈ P ρ s.1
    · simp only [q, post, if_pos h, ← Finset.mul_sum, h.1.2, mul_one]
    · simp [q, post, if_neg h, hz0 s h]
  have hqv : ∀ (ω : Ω) (s : S), q (ω, s) * v ω (act s) = q (ω, s) * v ω s.1 := by
    intro ω s
    by_cases h : z s.1 s.2 ∈ P ρ s.1
    · simp [act, if_pos h]
    · simp [q, hz0 s h]
  let π : Measure (Ω × S) := ∑ p, ENNReal.ofReal (q p) • Measure.dirac p
  have hπ : ∀ E : Set (Ω × S), π E = ENNReal.ofReal (∑ p, E.indicator q p) := by
    intro E
    rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => Set.indicator_nonneg (fun p _ => hq0 p) p)]
    simp only [π, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
      Measure.dirac_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p ∈ E <;> simp [hp]
  have hπR : ∀ E : Set (Ω × S), (π E).toReal = ∑ p, E.indicator q p := fun E => by
    rw [hπ E, ENNReal.toReal_ofReal
      (Finset.sum_nonneg fun p _ => Set.indicator_nonneg (fun p _ => hq0 p) p)]
  have htot : ∑ p, q p = 1 := by
    rw [Fintype.sum_prod_type]; simp_rw [hrow]; exact hμ.2
  have hprob : IsProbabilityMeasure π :=
    ⟨by rw [hπ, Set.indicator_univ, htot, ENNReal.ofReal_one]⟩
  have hsing : ∀ p, π.real {p} = q p := by
    intro p; rw [measureReal_def, hπR]; simp only [Set.indicator_apply, Set.mem_singleton_iff]
    rw [Finset.sum_eq_single p (fun b _ hb => if_neg hb) (by simp)]; exact if_pos rfl
  have hνs : ∀ s : S, (π.map Prod.snd).real {s} = ∑ ω, q (ω, s) := by
    intro s
    rw [measureReal_def, Measure.map_apply measurable_snd (measurableSet_singleton s), hπR,
      Fintype.sum_prod_type]
    simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.sum_eq_single s (fun b _ hb => if_neg hb) (by simp)]; exact if_pos rfl
  refine ⟨S, mS, π, post, act, ⟨⟨hprob, fun ω => ?_⟩, ⟨fun s => ?_, fun ω => ?_,
    fun ω B hB => ?_⟩, fun s => ?_, fun b => MeasurableSpace.measurableSet_top⟩, ?_⟩
  · rw [hπ, Fintype.sum_prod_type, Finset.sum_eq_single ω]
    · simp [Set.indicator_apply, Set.mem_prod, hrow]
    · intro ω' _ hω'
      refine Finset.sum_eq_zero fun s _ => ?_
      simp [Set.indicator_apply, Set.mem_prod, hω']
    · simp
  · by_cases h : z s.1 s.2 ∈ P ρ s.1
    · simp only [post, if_pos h]; exact h.1
    · simp only [post, if_neg h]; exact hμ
  · exact fun _ _ => MeasurableSpace.measurableSet_top
  · rw [hπR, ← integral_indicator hB, integral_fintype Integrable.of_finite,
      Fintype.sum_prod_type, Finset.sum_eq_single ω]
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [hνs, smul_eq_mul]
      by_cases hs : s ∈ B
      · simp only [Set.indicator_apply, Set.mem_prod, Set.mem_singleton_iff, hs, and_true,
          if_true]
        exact hqz s ω
      · simp [Set.indicator_apply, Set.mem_prod, hs]
    · intro ω' _ hω'
      refine Finset.sum_eq_zero fun s _ => ?_
      simp [Set.indicator_apply, Set.mem_prod, hω']
    · simp
  · by_cases h : z s.1 s.2 ∈ P ρ s.1
    · simp only [post, act, if_pos h]; exact h
    · simp only [post, act, if_neg h]; exact hμP
  · show senderValue v π act = objective7 v t
    unfold senderValue objective7
    rw [integral_fintype Integrable.of_finite, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only [hsing, smul_eq_mul, hqv ω]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← htb b ω, Finset.sum_mul]

end RPConvexAux

open RiskPersuasion.Convex in
theorem solution {Ω A : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Fintype A] [Nonempty A]
    (μstar : Ω → ℝ) (hμ : μstar ∈ stdSimplex ℝ Ω) (ρ : (Ω → ℝ) → A → ℝ) (v : Ω → A → ℝ)
    (hP : ∀ a : A, IsClosed (P ρ a)) :
    achievableValues μstar ρ v = objective7 v '' {t | Feasible7 μstar ρ t} := by
  exact Set.Subset.antisymm (RPConvexAux.subset_dir μstar hμ ρ v hP)
    (RPConvexAux.supset_dir μstar hμ ρ v)
