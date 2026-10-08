-- Prove2me | solution 1 for OptimalPAC.SampleComplexity.chernoff_count_lower
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T19:24:44.433329+00:00
-- url     : https://prove2.me/submissions/9b75ba54-4969-44a3-b1e9-eb8be7ef6afb

import Mathlib

set_option autoImplicit false

namespace Chernoff5ec3b2ae

/-- `exp (-0.363) ≤ 7/10`. -/
lemma exp_neg_le : Real.exp (-(363 / 1000 : ℝ)) ≤ 7 / 10 := by
  have h := Real.quadratic_le_exp_of_nonneg (x := (363 / 1000 : ℝ)) (by norm_num)
  have h1 : Real.exp (-(363 / 1000 : ℝ)) * Real.exp (363 / 1000) = 1 := by
    rw [← Real.exp_add]; simp
  have hc0 := Real.exp_pos (-(363 / 1000 : ℝ))
  have he0 := Real.exp_pos (363 / 1000 : ℝ)
  nlinarith

/-- The final real inequality. -/
lemma final_real (c q L δ : ℝ) (n : ℕ) (hc0 : 0 < c) (hc1 : c ≤ 7 / 10)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hL0 : 0 < L) (hL : Real.exp (-L) = δ / 9)
    (hqn : 23 * L ≤ q * n) :
    (c * q + (1 - q)) ^ n ≤
      Real.exp (-(363 / 1000 : ℝ) * (7 / 10 * q * n)) * (δ / 9) := by
  have hb0 : 0 ≤ c * q + (1 - q) := by nlinarith
  have hb1 : c * q + (1 - q) ≤ Real.exp (-(3 / 10) * q) := by
    have := Real.add_one_le_exp (-(3 / 10) * q)
    nlinarith
  have hpow : (c * q + (1 - q)) ^ n ≤ Real.exp (n * (-(3 / 10) * q)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hb0 hb1 n
  refine hpow.trans ?_
  rw [← hL, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

end Chernoff5ec3b2ae

open MeasureTheory in
theorem solution {X : Type*} [MeasurableSpace X] (Q : Measure X)
    [IsProbabilityMeasure Q] (E : Set X) (hE : MeasurableSet E) (n : ℕ) (hn : 1 ≤ n)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hQE : 23 / (n : ℝ) * Real.log (9 / δ) ≤ (Q E).toReal) :
    Measure.pi (fun _ : Fin n => Q)
      {z | (({t : Fin n | z t ∈ E}.ncard : ℕ) : ℝ) < 7 / 10 * (Q E).toReal * n}
      ≤ ENNReal.ofReal (δ / 9) := by
  classical
  set q : ℝ := (Q E).toReal with hq
  set P : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => Q) with hP
  set c : ℝ := Real.exp (-(363 / 1000 : ℝ)) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c ≤ 7 / 10 := Chernoff5ec3b2ae.exp_neg_le
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hq1 : q ≤ 1 := by
    rw [hq]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  let f : X → ℝ := fun x => if x ∈ E then c else 1
  have hfm : Measurable f := Measurable.ite hE measurable_const measurable_const
  have hf0 : ∀ x, 0 ≤ f x := fun x => by
    simp only [f]; split_ifs <;> linarith
  have hf1 : ∀ x, f x ≤ 1 := fun x => by
    simp only [f]; split_ifs <;> linarith
  let g : (Fin n → X) → ℝ := fun z => ∏ t, f (z t)
  have hgm : Measurable g :=
    Finset.measurable_prod _ (fun t _ => hfm.comp (measurable_pi_apply t))
  have hg0 : ∀ z, 0 ≤ g z := fun z => Finset.prod_nonneg (fun t _ => hf0 _)
  have hg1 : ∀ z, g z ≤ 1 := fun z =>
    Finset.prod_le_one (fun t _ => hf0 _) (fun t _ => hf1 _)
  have hgint : Integrable g P :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 z)]; exact hg1 z)
  have hfint : ∫ x, f x ∂Q = c * q + (1 - q) := by
    have hfe : f = E.piecewise (fun _ => c) (fun _ => 1) := by
      ext x; simp [f, Set.piecewise]
    rw [hfe, integral_piecewise hE (integrable_const _).integrableOn
      (integrable_const _).integrableOn, setIntegral_const, setIntegral_const,
      probReal_compl_eq_one_sub hE]
    simp [q, measureReal_def]
    ring
  have hgI : ∫ z, g z ∂P = (c * q + (1 - q)) ^ n := by
    rw [← hfint]
    have := integral_fintype_prod_eq_pow (ι := Fin n) (μ := Q) f
    simpa [g, P, Fintype.card_fin] using this
  -- g z = c ^ N z
  have hgN : ∀ z : Fin n → X, g z = c ^ ({t : Fin n | z t ∈ E}.ncard) := by
    intro z
    have hcard : ({t : Fin n | z t ∈ E}.ncard) =
        (Finset.univ.filter (fun t => z t ∈ E)).card := by
      rw [← Set.ncard_coe_finset]; congr 1; ext t; simp
    simp only [g, f]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, hcard]
  set k : ℝ := Real.exp (-(363 / 1000 : ℝ) * (7 / 10 * q * n)) with hk
  have hk0 : 0 < k := Real.exp_pos _
  have hsub : {z : Fin n → X | (({t : Fin n | z t ∈ E}.ncard : ℕ) : ℝ) < 7 / 10 * q * n}
      ⊆ {z | k ≤ g z} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    rw [hgN, hc, ← Real.exp_nat_mul, hk]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hg0) hgint k
  rw [hgI] at hmk
  -- the real bound
  set L : ℝ := Real.log (9 / δ) with hLdef
  have hL0 : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hL : Real.exp (-L) = δ / 9 := by
    rw [Real.exp_neg, hLdef, Real.exp_log (by positivity)]; field_simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hqn : 23 * L ≤ q * n := by
    have := mul_le_mul_of_nonneg_right hQE hnpos.le
    have e : 23 / (n : ℝ) * L * n = 23 * L := by field_simp
    have e2 : 23 * (L / (n : ℝ)) * n = 23 * L := by field_simp
    linarith
  have hfin := Chernoff5ec3b2ae.final_real c q L δ n hc0 hc1 hq0 hq1 hL0 hL hqn
  have hreal : P.real {z | k ≤ g z} ≤ δ / 9 := by
    have h1 : k * P.real {z | k ≤ g z} ≤ k * (δ / 9) := by
      calc k * P.real {z | k ≤ g z} ≤ (c * q + (1 - q)) ^ n := hmk
        _ ≤ k * (δ / 9) := hfin
    exact le_of_mul_le_mul_left h1 hk0
  calc P {z | (({t : Fin n | z t ∈ E}.ncard : ℕ) : ℝ) < 7 / 10 * q * n}
      ≤ P {z | k ≤ g z} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {z | k ≤ g z}) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (δ / 9) := ENNReal.ofReal_le_ofReal hreal
