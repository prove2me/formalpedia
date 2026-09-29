-- Prove2me | solution 1 for StochasticOrders.PositiveDependence.pqd_order_convolution
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T23:51:13.567177+00:00
-- url     : https://prove2.me/submissions/486c82f3-fb79-4966-b074-8490beec7497

import Mathlib
import Definitions.Def_StochasticOrders_PositiveDependence_Orders

/-! Disproof of acc27b86 `StochasticOrders.PositiveDependence.pqd_order_convolution`.

The laws are arbitrary `Measure`s, and `survivalVec`/`cdfVec` take `toReal`, so an infinite
orthant mass reads as `0`. Take `n = 1`, `Py = 0`, `Pu = Pv = dirac 0`, `φ₀ x u = 1[0 ≤ x]`
(monotone, measurable) and `Px = dirac 0 + ⊤ • volume|{y₀ < 0}`. Every open upper orthant
and every closed lower orthant has `Px`-mass `0` or `⊤`, so `PQDOrder Px 0` holds. But the
closed upper orthant `{0 ≤ x₀}` has mass exactly `1`, so the left law of the conclusion,
the pushforward of `Px ⊗ δ₀` under `φ`, gives `{y₀ > 1/2}` survival mass `1`, while the right
law is `0`. So `1 ≤ 0`. -/

set_option autoImplicit false

open MeasureTheory StochasticOrders.PositiveDependence

noncomputable def pqdMu_acc2 : Measure (Fin 1 → ℝ) :=
  Measure.dirac 0 + (⊤ : ENNReal) • (volume : Measure (Fin 1 → ℝ)).restrict {y | ∀ i, y i < 0}

theorem pqd_neg_meas_acc2 : MeasurableSet {y : Fin 1 → ℝ | ∀ i, y i < 0} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => measurableSet_lt (measurable_pi_apply i) measurable_const

theorem pqd_top_of_box_acc2 (S : Set (Fin 1 → ℝ)) (hS : MeasurableSet S) (a b : ℝ) (hab : a < b)
    (hb : b ≤ 0) (hsub : Set.pi Set.univ (fun _ : Fin 1 => Set.Ioo a b) ⊆ S) :
    pqdMu_acc2 S = ⊤ := by
  apply le_antisymm le_top
  have hsub' : Set.pi Set.univ (fun _ : Fin 1 => Set.Ioo a b) ⊆ S ∩ {y | ∀ i, y i < 0} := by
    intro y hy
    refine ⟨hsub hy, fun i => ?_⟩
    have := (hy i (Set.mem_univ i)).2
    linarith
  have hvol : volume (Set.pi Set.univ (fun _ : Fin 1 => Set.Ioo a b)) = ENNReal.ofReal (b - a) := by
    rw [Real.volume_pi_Ioo]; simp
  have hpos : ENNReal.ofReal (b - a) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  calc (⊤ : ENNReal) = (⊤ : ENNReal) * volume (Set.pi Set.univ (fun _ : Fin 1 => Set.Ioo a b)) := by
        rw [hvol, ENNReal.top_mul hpos]
    _ ≤ (⊤ : ENNReal) * volume (S ∩ {y | ∀ i, y i < 0}) := by gcongr
    _ = ((⊤ : ENNReal) • (volume : Measure (Fin 1 → ℝ)).restrict {y | ∀ i, y i < 0}) S := by
        rw [Measure.smul_apply, Measure.restrict_apply hS, smul_eq_mul]
    _ ≤ pqdMu_acc2 S := by
        rw [pqdMu_acc2, Measure.add_apply]; exact le_add_self

theorem pqd_hXY_acc2 : PQDOrder pqdMu_acc2 (0 : Measure (Fin 1 → ℝ)) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have hS : MeasurableSet {y : Fin 1 → ℝ | ∀ i, x i < y i} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)
    have h : pqdMu_acc2 {y : Fin 1 → ℝ | ∀ i, x i < y i} = 0 ∨
        pqdMu_acc2 {y : Fin 1 → ℝ | ∀ i, x i < y i} = ⊤ := by
      by_cases hx : x 0 < 0
      · right
        refine pqd_top_of_box_acc2 _ hS (x 0) 0 hx le_rfl ?_
        intro y hy i
        fin_cases i
        exact (hy 0 (Set.mem_univ _)).1
      · left
        rw [pqdMu_acc2, Measure.add_apply, Measure.smul_apply, Measure.restrict_apply hS]
        have h1 : {y : Fin 1 → ℝ | ∀ i, x i < y i} ∩ {y | ∀ i, y i < 0} = ∅ := by
          ext y
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
            not_and]
          intro h1 h2
          have := h1 0
          have := h2 0
          linarith [not_lt.mp hx]
        rw [h1, measure_empty, smul_zero, add_zero, Measure.dirac_apply' _ hS]
        simp [Fin.forall_fin_one, hx]
    show (pqdMu_acc2 {y | ∀ i, x i < y i}).toReal ≤
      ((0 : Measure (Fin 1 → ℝ)) {y | ∀ i, x i < y i}).toReal
    rw [Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero]
    rcases h with h | h <;> rw [h] <;> simp
  · have hS : MeasurableSet {y : Fin 1 → ℝ | ∀ i, y i ≤ x i} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i) measurable_const
    have h : pqdMu_acc2 {y : Fin 1 → ℝ | ∀ i, y i ≤ x i} = ⊤ := by
      refine pqd_top_of_box_acc2 _ hS (min (x 0) 0 - 1) (min (x 0) 0) (by linarith)
        (min_le_right _ _) ?_
      intro y hy i
      fin_cases i
      have := (hy 0 (Set.mem_univ _)).2
      have := min_le_left (x 0) 0
      show y 0 ≤ x 0
      linarith
    simp only [cdfVec, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero, h,
      ENNReal.toReal_top, le_refl]

open MeasureTheory StochasticOrders.PositiveDependence in
theorem solution : ¬ (∀ {n : ℕ} (Px Py Pu Pv : Measure (Fin n → ℝ))
    (hXY : PQDOrder Px Py) (hUV : PQDOrder Pu Pv)
    (φ : Fin n → ℝ → ℝ → ℝ) (hφ : ∀ i, Monotone (Function.uncurry (φ i)))
    (hφm : ∀ i, Measurable (Function.uncurry (φ i))),
    PQDOrder
      (Measure.map (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => φ i (p.1 i) (p.2 i))
        (Px.prod Pu))
      (Measure.map (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => φ i (p.1 i) (p.2 i))
        (Py.prod Pv))) := by
  intro H
  let φ : Fin 1 → ℝ → ℝ → ℝ := fun _ x _ => if 0 ≤ x then 1 else 0
  have hφ : ∀ i, Monotone (Function.uncurry (φ i)) := by
    intro i p q hpq
    have h1 : p.1 ≤ q.1 := hpq.1
    simp only [Function.uncurry, φ]
    split_ifs with ha hb hb <;> linarith
  have hφm : ∀ i, Measurable (Function.uncurry (φ i)) := by
    intro i
    exact Measurable.ite (measurableSet_le measurable_const measurable_fst)
      measurable_const measurable_const
  have hUV : PQDOrder (Measure.dirac (0 : Fin 1 → ℝ)) (Measure.dirac 0) :=
    ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  have hc := (H pqdMu_acc2 0 (Measure.dirac 0) (Measure.dirac 0) pqd_hXY_acc2 hUV φ hφ hφm).1
    (fun _ => 1 / 2)
  have hF : Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => fun i => φ i (p.1 i) (p.2 i)) := by
    refine measurable_pi_lambda _ (fun i => ?_)
    have hm : Measurable (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => (p.1 i, p.2 i)) := by fun_prop
    exact (hφm i).comp hm
  have hT : MeasurableSet {y : Fin 1 → ℝ | ∀ i, (fun _ => (1 : ℝ) / 2) i < y i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)
  have hpre : (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => fun i => φ i (p.1 i) (p.2 i)) ⁻¹'
      {y : Fin 1 → ℝ | ∀ i, (fun _ => (1 : ℝ) / 2) i < y i} =
      {x : Fin 1 → ℝ | 0 ≤ x 0} ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Fin.forall_fin_one, Set.mem_prod,
      Set.mem_univ, and_true, φ]
    split_ifs with h <;> simp [h] <;> norm_num
  have hA : MeasurableSet {x : Fin 1 → ℝ | 0 ≤ x 0} :=
    measurableSet_le measurable_const (measurable_pi_apply 0)
  have hL : survivalVec (Measure.map (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
      fun i => φ i (p.1 i) (p.2 i)) (pqdMu_acc2.prod (Measure.dirac 0))) (fun _ => 1 / 2) = 1 := by
    rw [survivalVec, Measure.map_apply hF hT, hpre, Measure.prod_prod, measure_univ, mul_one,
      pqdMu_acc2, Measure.add_apply, Measure.smul_apply, Measure.restrict_apply hA]
    have h1 : {x : Fin 1 → ℝ | 0 ≤ x 0} ∩ {y | ∀ i, y i < 0} = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      have := h2 0
      linarith
    rw [h1, measure_empty, smul_zero, add_zero, Measure.dirac_apply' _ hA]
    simp
  have hR : survivalVec (Measure.map (fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
      fun i => φ i (p.1 i) (p.2 i)) ((0 : Measure (Fin 1 → ℝ)).prod (Measure.dirac 0)))
      (fun _ => 1 / 2) = 0 := by
    rw [Measure.zero_prod, Measure.map_zero]
    simp [survivalVec]
  rw [hL, hR] at hc
  norm_num at hc
