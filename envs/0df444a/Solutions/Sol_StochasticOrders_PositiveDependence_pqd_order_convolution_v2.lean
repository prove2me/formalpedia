-- Prove2me | solution 1 for StochasticOrders.PositiveDependence.pqd_order_convolution_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T08:11:48.793425+00:00
-- url     : https://prove2.me/submissions/a6bb3345-ea57-4bbc-9f86-82816c87527d

import Mathlib
import Definitions.Def_StochasticOrders_PositiveDependence_Orders

namespace PQ88

open MeasureTheory Filter Topology StochasticOrders.PositiveDependence

lemma upper_approx (S : Set ℝ) (hS : IsUpperSet S) :
    ∃ a : ℕ → ℝ, ∀ x, ∀ᶠ k in atTop, (a k < x ↔ x ∈ S) := by
  by_cases hne : S.Nonempty
  · by_cases hb : BddBelow S
    · by_cases hs : sInf S ∈ S
      · refine ⟨fun k => sInf S - 1 / ((k:ℝ) + 1), fun x => ?_⟩
        by_cases hx : x ∈ S
        · refine Eventually.of_forall fun k => ?_
          have h1 := csInf_le hb hx
          have : (0:ℝ) < 1 / ((k:ℝ) + 1) := by positivity
          simp only [hx, iff_true]; linarith
        · have hxs : x < sInf S := by
            by_contra h; push Not at h; exact hx (hS h hs)
          have ht : Tendsto (fun k : ℕ => sInf S - 1 / ((k:ℝ) + 1)) atTop (𝓝 (sInf S - 0)) :=
            tendsto_one_div_add_atTop_nhds_zero_nat.const_sub _
          rw [sub_zero] at ht
          filter_upwards [(tendsto_order.1 ht).1 x hxs] with k hk
          simp only [hx, iff_false, not_lt]; exact hk.le
      · refine ⟨fun _ => sInf S, fun x => Eventually.of_forall fun _ => ?_⟩
        constructor
        · intro h
          obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hne h
          exact hS hyx.le hy
        · intro hx
          dsimp only
          exact lt_of_le_of_ne (csInf_le hb hx) (fun h => hs (by rw [h]; exact hx))
    · refine ⟨fun k => -(k:ℝ), fun x => ?_⟩
      have hx : x ∈ S := by
        rw [not_bddBelow_iff] at hb
        obtain ⟨y, hy, hyx⟩ := hb x
        exact hS hyx.le hy
      obtain ⟨N, hN⟩ := exists_nat_gt (-x)
      refine eventually_atTop.2 ⟨N, fun k hk => ?_⟩
      simp only [hx, iff_true]
      have : (N:ℝ) ≤ k := by exact_mod_cast hk
      linarith
  · refine ⟨fun k => (k:ℝ), fun x => ?_⟩
    rw [Set.not_nonempty_iff_eq_empty] at hne
    obtain ⟨N, hN⟩ := exists_nat_gt x
    refine eventually_atTop.2 ⟨N, fun k hk => ?_⟩
    simp only [hne, Set.mem_empty_iff_false, iff_false, not_lt]
    have : (N:ℝ) ≤ k := by exact_mod_cast hk
    linarith

lemma lower_approx (S : Set ℝ) (hS : IsLowerSet S) :
    ∃ a : ℕ → ℝ, ∀ x, ∀ᶠ k in atTop, (x ≤ a k ↔ x ∈ S) := by
  obtain ⟨a, ha⟩ := upper_approx Sᶜ hS.compl
  refine ⟨a, fun x => (ha x).mono fun k hk => ?_⟩
  rw [← not_lt, hk, Set.mem_compl_iff, not_not]

variable {ι : Type*} [Fintype ι]

lemma upper_gen (P Q : Measure (ι → ℝ)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ x, survivalVec P x ≤ survivalVec Q x) (S : ι → Set ℝ) (hS : ∀ i, IsUpperSet (S i)) :
    P {y | ∀ i, y i ∈ S i} ≤ Q {y | ∀ i, y i ∈ S i} := by
  choose a ha using fun i => upper_approx (S i) (hS i)
  have hlim : ∀ y : ι → ℝ, ∀ᶠ k in atTop,
      y ∈ {y : ι → ℝ | ∀ i, (fun i => a i k) i < y i} ↔ y ∈ {y : ι → ℝ | ∀ i, y i ∈ S i} := by
    intro y
    filter_upwards [eventually_all.2 fun i => ha i (y i)] with k hk
    exact forall_congr' hk
  have hm : ∀ k : ℕ, MeasurableSet {y : ι → ℝ | ∀ i, (fun i => a i k) i < y i} := by
    intro k
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)
  have tP := tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure atTop P hm hlim
  have tQ := tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure atTop Q hm hlim
  refine le_of_tendsto_of_tendsto' tP tQ fun k => ?_
  have := h (fun i => a i k)
  unfold survivalVec at this
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 this

lemma lower_gen (P Q : Measure (ι → ℝ)) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ x, cdfVec P x ≤ cdfVec Q x) (S : ι → Set ℝ) (hS : ∀ i, IsLowerSet (S i)) :
    P {y | ∀ i, y i ∈ S i} ≤ Q {y | ∀ i, y i ∈ S i} := by
  choose a ha using fun i => lower_approx (S i) (hS i)
  have hlim : ∀ y : ι → ℝ, ∀ᶠ k in atTop,
      y ∈ {y : ι → ℝ | ∀ i, y i ≤ (fun i => a i k) i} ↔ y ∈ {y : ι → ℝ | ∀ i, y i ∈ S i} := by
    intro y
    filter_upwards [eventually_all.2 fun i => ha i (y i)] with k hk
    exact forall_congr' hk
  have hm : ∀ k : ℕ, MeasurableSet {y : ι → ℝ | ∀ i, y i ≤ (fun i => a i k) i} := by
    intro k
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i) measurable_const
  have tP := tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure atTop P hm hlim
  have tQ := tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure atTop Q hm hlim
  refine le_of_tendsto_of_tendsto' tP tQ fun k => ?_
  have := h (fun i => a i k)
  unfold cdfVec at this
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 this

lemma step_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P Q : Measure α) (R : Measure β) [SFinite P] [SFinite Q] [SFinite R]
    (E : Set (α × β)) (hE : MeasurableSet E)
    (h : ∀ u, P ((fun x => (x, u)) ⁻¹' E) ≤ Q ((fun x => (x, u)) ⁻¹' E)) :
    P.prod R E ≤ Q.prod R E := by
  rw [Measure.prod_apply_symm hE, Measure.prod_apply_symm hE]
  exact lintegral_mono h

lemma step_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (R : Measure α) (P Q : Measure β) [SFinite P] [SFinite Q] [SFinite R]
    (E : Set (α × β)) (hE : MeasurableSet E)
    (h : ∀ y, P (Prod.mk y ⁻¹' E) ≤ Q (Prod.mk y ⁻¹' E)) :
    R.prod P E ≤ R.prod Q E := by
  rw [Measure.prod_apply hE, Measure.prod_apply hE]
  exact lintegral_mono h

end PQ88

open StochasticOrders.PositiveDependence MeasureTheory in
theorem solution {n : ℕ} (Px Py Pu Pv : Measure (Fin n → ℝ))
    [IsProbabilityMeasure Px] [IsProbabilityMeasure Py] [IsProbabilityMeasure Pu]
    [IsProbabilityMeasure Pv]
    (hXY : PQDOrder Px Py) (hUV : PQDOrder Pu Pv)
    (φ : Fin n → ℝ → ℝ → ℝ) (hφ : ∀ i, Monotone (Function.uncurry (φ i)))
    (hφm : ∀ i, Measurable (Function.uncurry (φ i))) :
    PQDOrder
      (Measure.map (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => φ i (p.1 i) (p.2 i))
        (Px.prod Pu))
      (Measure.map (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => φ i (p.1 i) (p.2 i))
        (Py.prod Pv)) := by
  set F : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) := fun p i => φ i (p.1 i) (p.2 i) with hF
  have hFm : Measurable F := by
    refine measurable_pi_lambda _ fun i => ?_
    exact (hφm i).comp (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 i, p.2 i)) (by fun_prop)
  have mono1 : ∀ i (a b c : ℝ), a ≤ b → φ i a c ≤ φ i b c := fun i a b c hab =>
    hφ i (a := (a, c)) (b := (b, c)) (Prod.mk_le_mk.2 ⟨hab, le_rfl⟩)
  have mono2 : ∀ i (a b c : ℝ), a ≤ b → φ i c a ≤ φ i c b := fun i a b c hab =>
    hφ i (a := (c, a)) (b := (c, b)) (Prod.mk_le_mk.2 ⟨le_rfl, hab⟩)
  constructor
  · intro t
    unfold survivalVec
    have hO : MeasurableSet {y : Fin n → ℝ | ∀ i, t i < y i} := by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)
    rw [Measure.map_apply hFm hO, Measure.map_apply hFm hO]
    have hE := hFm hO
    refine (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 ?_
    refine le_trans (PQ88.step_left Px Py Pu _ hE fun u => ?_)
      (PQ88.step_right Py Pu Pv _ hE fun y => ?_)
    · exact PQ88.upper_gen Px Py hXY.1 (fun i => {a | t i < φ i a (u i)})
        (fun i a b hab ha => lt_of_lt_of_le ha (mono1 i a b _ hab))
    · exact PQ88.upper_gen Pu Pv hUV.1 (fun i => {a | t i < φ i (y i) a})
        (fun i a b hab ha => lt_of_lt_of_le ha (mono2 i a b _ hab))
  · intro t
    unfold cdfVec
    have hO : MeasurableSet {y : Fin n → ℝ | ∀ i, y i ≤ t i} := by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i) measurable_const
    rw [Measure.map_apply hFm hO, Measure.map_apply hFm hO]
    have hE := hFm hO
    refine (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 ?_
    refine le_trans (PQ88.step_left Px Py Pu _ hE fun u => ?_)
      (PQ88.step_right Py Pu Pv _ hE fun y => ?_)
    · exact PQ88.lower_gen Px Py hXY.2 (fun i => {a | φ i a (u i) ≤ t i})
        (fun i a b hab ha => le_trans (mono1 i b a _ hab) ha)
    · exact PQ88.lower_gen Pu Pv hUV.2 (fun i => {a | φ i (y i) a ≤ t i})
        (fun i a b hab ha => le_trans (mono2 i b a _ hab) ha)
