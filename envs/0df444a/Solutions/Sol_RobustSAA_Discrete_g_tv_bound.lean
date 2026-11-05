-- Prove2me | solution 1 for RobustSAA.Discrete.g_tv_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:30:57.872904+00:00
-- url     : https://prove2.me/submissions/aeca3d78-2715-45eb-88d8-f44395077e89

import Mathlib
import Definitions.Def_RobustSAA_Discrete_Setting

namespace RobustSAA.Discrete

open Real Set

/-- `h(u) = (u+1) log u - 2(u-1)` is monotone on `(0,∞)`. -/
lemma pinsker_h_mono :
    MonotoneOn (fun u : ℝ => (u + 1) * Real.log u - 2 * (u - 1)) (Ioi 0) := by
  have hd : ∀ u : ℝ, 0 < u → HasDerivAt (fun u : ℝ => (u + 1) * Real.log u - 2 * (u - 1))
      (Real.log u + (u + 1) / u - 2) u := by
    intro u hu
    have h1 : HasDerivAt (fun u : ℝ => u + 1) 1 u := (hasDerivAt_id u).add_const 1
    have h2 : HasDerivAt Real.log u⁻¹ u := Real.hasDerivAt_log hu.ne'
    have h3 := (h1.mul h2).sub (((hasDerivAt_id u).sub_const 1).const_mul 2)
    refine h3.congr_deriv ?_
    field_simp
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · intro u hu
    exact (hd u hu).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    exact (hd u hu).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    have hu' : (0:ℝ) < u := hu
    rw [(hd u hu).deriv]
    have hl := Real.one_sub_inv_le_log_of_pos hu
    have : (u + 1) / u = 1 + u⁻¹ := by field_simp
    rw [this]
    linarith

lemma pinsker_g_deriv (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => (2 * u + 4) * (u * Real.log u - u + 1) - 3 * (u - 1) ^ 2)
      (4 * ((u + 1) * Real.log u - 2 * (u - 1))) u := by
  have h1 : HasDerivAt (fun u : ℝ => 2 * u + 4) 2 u := by
    simpa using ((hasDerivAt_id u).const_mul 2).add_const 4
  have h2 : HasDerivAt (fun u : ℝ => u * Real.log u - u + 1) (Real.log u) u := by
    have := ((Real.hasDerivAt_mul_log hu.ne').sub (hasDerivAt_id u)).add_const 1
    exact this.congr_deriv (by ring)
  have h3 : HasDerivAt (fun u : ℝ => 3 * (u - 1) ^ 2) (3 * (2 * (u - 1))) u := by
    have := (((hasDerivAt_id u).sub_const 1).pow 2).const_mul 3
    exact this.congr_deriv (by simp)
  exact ((h1.mul h2).sub h3).congr_deriv (by ring)

/-- The scalar inequality behind Pinsker: `3 (u-1)^2 ≤ (2u+4)(u log u - u + 1)` for `u > 0`. -/
lemma pinsker_scalar (u : ℝ) (hu : 0 < u) :
    3 * (u - 1) ^ 2 ≤ (2 * u + 4) * (u * Real.log u - u + 1) := by
  set g : ℝ → ℝ := fun u => (2 * u + 4) * (u * Real.log u - u + 1) - 3 * (u - 1) ^ 2 with hg
  have hcont : ∀ v : ℝ, 0 < v → ContinuousAt g v :=
    fun v hv => (pinsker_g_deriv v hv).continuousAt
  have hdiff : ∀ v : ℝ, 0 < v → DifferentiableAt ℝ g v :=
    fun v hv => (pinsker_g_deriv v hv).differentiableAt
  have hh1 : ((1 : ℝ) + 1) * Real.log 1 - 2 * (1 - 1) = 0 := by simp
  have g1 : g 1 = 0 := by simp [hg]
  suffices 0 ≤ g u by simp only [hg] at this; linarith
  rcases le_total u 1 with h | h
  · -- g is antitone on (0,1]
    have hanti : AntitoneOn g (Ioc 0 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 1) ?_ ?_ ?_
      · intro v hv; exact (hcont v hv.1).continuousWithinAt
      · intro v hv
        rw [interior_Ioc] at hv
        exact (hdiff v hv.1).differentiableWithinAt
      · intro v hv
        rw [interior_Ioc] at hv
        rw [(pinsker_g_deriv v hv.1).deriv]
        have := pinsker_h_mono hv.1 (show (1:ℝ) ∈ Ioi 0 by norm_num) hv.2.le
        simp only at this
        linarith
    have := hanti ⟨hu, h⟩ ⟨one_pos, le_rfl⟩ h
    linarith
  · have hmono : MonotoneOn g (Ici 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 1) ?_ ?_ ?_
      · intro v hv
        exact (hcont v (lt_of_lt_of_le one_pos hv)).continuousWithinAt
      · intro v hv
        rw [interior_Ici] at hv
        exact (hdiff v (lt_trans one_pos hv)).differentiableWithinAt
      · intro v hv
        rw [interior_Ici] at hv
        rw [(pinsker_g_deriv v (lt_trans one_pos hv)).deriv]
        have := pinsker_h_mono (show (1:ℝ) ∈ Ioi 0 by norm_num)
          (show v ∈ Ioi 0 from (lt_trans one_pos hv : (0:ℝ) < v)) hv.le
        simp only at this
        linarith
    have := hmono (show (1:ℝ) ∈ Ici 1 from (le_refl (1:ℝ))) (show u ∈ Ici 1 from h) h
    linarith

/-- Two-variable form: for `p > 0`, `q > 0`,
`3 (q - p)^2 ≤ (2q + 4p) (q log (q/p) - q + p)`. -/
lemma pinsker_pointwise (q p : ℝ) (hq : 0 < q) (hp : 0 < p) :
    3 * (q - p) ^ 2 ≤ (2 * q + 4 * p) * (q * Real.log (q / p) - q + p) := by
  have h := pinsker_scalar (q / p) (div_pos hq hp)
  have hp2 : 0 < p ^ 2 := by positivity
  have e1 : 3 * (q - p) ^ 2 = p ^ 2 * (3 * (q / p - 1) ^ 2) := by
    field_simp
  have e2 : (2 * q + 4 * p) * (q * Real.log (q / p) - q + p) =
      p ^ 2 * ((2 * (q / p) + 4) * (q / p * Real.log (q / p) - q / p + 1)) := by
    field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left h hp2.le

/-- Pinsker's inequality for finite probability vectors, in the form
`(∑ |q - p|)^2 ≤ 2 ∑_{q_j > 0} q_j log (q_j / p_j)`. -/
lemma pinsker_vec {n : ℕ} (q p : Fin n → ℝ) (hq0 : ∀ j, 0 ≤ q j) (hp0 : ∀ j, 0 ≤ p j)
    (hsq : ∑ j, q j = 1) (hsp : ∑ j, p j = 1) (hsupp : ∀ j, q j ≠ 0 → p j ≠ 0) :
    (∑ j, |q j - p j|) ^ 2 ≤
      2 * ∑ j, (if q j = 0 then 0 else q j * Real.log (q j / p j)) := by
  set K : Fin n → ℝ := fun j => if q j = 0 then 0 else q j * Real.log (q j / p j) with hK
  set d : Fin n → ℝ := fun j => K j - q j + p j with hd
  set c : Fin n → ℝ := fun j => (2 * q j + 4 * p j) / 3 with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j => by
    simp only [hc]; have := hq0 j; have := hp0 j; positivity
  have hpt : ∀ j, 0 ≤ d j ∧ (q j - p j) ^ 2 ≤ c j * d j := by
    intro j
    by_cases hqj : q j = 0
    · have hdj : d j = p j := by simp [hd, hK, hqj]
      have hcj : c j = 4 * p j / 3 := by simp [hc, hqj]
      rw [hdj, hcj, hqj]
      have := hp0 j
      constructor
      · exact this
      · nlinarith
    · have hqpos : 0 < q j := lt_of_le_of_ne (hq0 j) (Ne.symm hqj)
      have hppos : 0 < p j := lt_of_le_of_ne (hp0 j) (Ne.symm (hsupp j hqj))
      have hdj : d j = q j * Real.log (q j / p j) - q j + p j := by simp [hd, hK, hqj]
      have key := pinsker_pointwise (q j) (p j) hqpos hppos
      rw [← hdj] at key
      have hpos : 0 < 2 * q j + 4 * p j := by linarith
      have hd0 : 0 ≤ d j := by
        by_contra hneg
        push Not at hneg
        have : (2 * q j + 4 * p j) * d j < 0 := mul_neg_of_pos_of_neg hpos hneg
        nlinarith [sq_nonneg (q j - p j)]
      refine ⟨hd0, ?_⟩
      simp only [hc]
      nlinarith
  have habs : ∀ j, |q j - p j| ≤ Real.sqrt (c j) * Real.sqrt (d j) := by
    intro j
    rw [← Real.sqrt_mul (hc0 j), ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (hpt j).2
  have hsumc : ∑ j, c j = 2 := by
    simp only [hc]
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsq, hsp]
    norm_num
  have hsumd : ∑ j, d j = ∑ j, K j := by
    simp only [hd]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsq, hsp]
    ring
  have hS0 : 0 ≤ ∑ j, K j := by
    rw [← hsumd]; exact Finset.sum_nonneg (fun j _ => (hpt j).1)
  have h1 : ∑ j, |q j - p j| ≤ Real.sqrt 2 * Real.sqrt (∑ j, K j) := by
    calc ∑ j, |q j - p j| ≤ ∑ j, Real.sqrt (c j) * Real.sqrt (d j) :=
          Finset.sum_le_sum (fun j _ => habs j)
      _ ≤ Real.sqrt (∑ j, c j) * Real.sqrt (∑ j, d j) :=
          Real.sum_sqrt_mul_sqrt_le _ hc0 (fun j => (hpt j).1)
      _ = Real.sqrt 2 * Real.sqrt (∑ j, K j) := by rw [hsumc, hsumd]
  have h0 : 0 ≤ ∑ j, |q j - p j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  calc (∑ j, |q j - p j|) ^ 2 ≤ (Real.sqrt 2 * Real.sqrt (∑ j, K j)) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
    _ = 2 * ∑ j, K j := by
        rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hS0]

lemma phat_nonneg {n N : ℕ} (s : Fin N → Fin n) (j : Fin n) : 0 ≤ phat s j := by
  unfold phat; positivity

lemma sum_phat {n N : ℕ} (hN : 0 < N) (s : Fin N → Fin n) : ∑ j, phat s j = 1 := by
  unfold phat
  rw [← Finset.sum_div]
  have : ∑ j : Fin n, ((Finset.univ.filter (fun i => s i = j)).card : ℝ) = N := by
    rw [← Nat.cast_sum]
    rw [← Finset.card_eq_sum_card_fiberwise (f := s) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    simp
  rw [this]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

lemma pvec_nonneg {n : ℕ} (F : MeasureTheory.ProbabilityMeasure (Fin n)) (j : Fin n) :
    0 ≤ pvec F j := by
  unfold pvec; exact MeasureTheory.measureReal_nonneg

lemma sum_pvec {n : ℕ} (F : MeasureTheory.ProbabilityMeasure (Fin n)) : ∑ j, pvec F j = 1 := by
  unfold pvec
  rw [MeasureTheory.sum_measureReal_singleton]
  simp

lemma gTerm_ne_bot {n N : ℕ} (F₀ : MeasureTheory.ProbabilityMeasure (Fin n))
    (s : Fin N → Fin n) (j : Fin n) : gTerm F₀ s j ≠ ⊥ := by
  unfold gTerm
  split_ifs
  · simp
  · simp
  · exact EReal.coe_ne_bot _

lemma ereal_coe_sum {n : ℕ} (K : Fin n → ℝ) : ((∑ j, K j : ℝ) : EReal) = ∑ j, (K j : EReal) := by
  let φ : ℝ →+ EReal := ⟨⟨(fun x : ℝ => (x : EReal)), EReal.coe_zero⟩, EReal.coe_add⟩
  exact map_sum φ K Finset.univ

lemma g_tv_bound_proof {n N : ℕ} (hN : 0 < N) (F₀ : MeasureTheory.ProbabilityMeasure (Fin n))
    (s : Fin N → Fin n) :
    ((dTV (phat s) (pvec F₀)) ^ 2 : EReal) ≤
      (∑ j : Fin n, gTerm F₀ s j) / 2 := by
  by_cases htop : ∃ j, phat s j ≠ 0 ∧ pvec F₀ j = 0
  · obtain ⟨j, hj1, hj2⟩ := htop
    have hgj : gTerm F₀ s j = ⊤ := by simp [gTerm, hj1, hj2]
    have hrest : ∑ k ∈ Finset.univ.erase j, gTerm F₀ s k ≠ ⊥ := by
      refine Finset.sum_induction _ (fun x => x ≠ ⊥) ?_ ?_ ?_
      · intro a b ha hb; exact EReal.add_ne_bot_iff.2 ⟨ha, hb⟩
      · simp
      · intro k _; exact gTerm_ne_bot F₀ s k
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hgj, EReal.top_add_of_ne_bot hrest,
      EReal.top_div_of_pos_ne_top (a := 2) (by norm_num)
      (by simpa using EReal.natCast_ne_top 2)]
    exact le_top
  · push Not at htop
    set K : Fin n → ℝ := fun j => if phat s j = 0 then 0
      else phat s j * Real.log (phat s j / pvec F₀ j) with hK
    have hg : ∀ j, gTerm F₀ s j = (K j : EReal) := by
      intro j
      by_cases h1 : phat s j = 0
      · simp [gTerm, hK, h1]
      · have h2 : pvec F₀ j ≠ 0 := htop j h1
        simp [gTerm, hK, h1, h2]
    simp_rw [hg]
    rw [← ereal_coe_sum, ← EReal.coe_pow, show (2 : EReal) = ((2 : ℝ) : EReal) from rfl,
      ← EReal.coe_div, EReal.coe_le_coe_iff]
    have hP := pinsker_vec (phat s) (pvec F₀) (phat_nonneg s) (pvec_nonneg F₀)
      (sum_phat hN s) (sum_pvec F₀) htop
    unfold dTV
    rw [mul_pow]
    have : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
    rw [this]
    simp only [hK]
    linarith

end RobustSAA.Discrete

open RobustSAA.Discrete MeasureTheory in
theorem solution {n N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure (Fin n))
    (s : Fin N → Fin n) :
    ((dTV (phat s) (pvec F₀)) ^ 2 : EReal) ≤
      (∑ j : Fin n, gTerm F₀ s j) / 2 :=
  g_tv_bound_proof hN F₀ s
