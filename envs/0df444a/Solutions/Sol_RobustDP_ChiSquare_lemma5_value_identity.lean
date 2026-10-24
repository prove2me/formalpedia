-- Prove2me | solution 1 for RobustDP.ChiSquare.lemma5_value_identity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T18:09:47.47905+00:00
-- url     : https://prove2.me/submissions/7d21da4d-69a8-4d53-9adb-ab229c277d40

import Mathlib
import Definitions.Def_RobustDP_ChiSquare_Moments
import Definitions.Def_RobustDP_ChiSquare_ChiSqSet

set_option autoImplicit false

namespace RobustDP.ChiSquare

/-- Weak duality: every dual value is below every primal value. -/
lemma l5aux_weak {S : Type*} [Fintype S] (q : S → ℝ) (hq : q ∈ stdSimplex ℝ S)
    (hq_pos : ∀ s, 0 < q s) (t : ℝ) (v p : S → ℝ) (hp : p ∈ chiSqSet q t)
    (μ : S → ℝ) (hμ : 0 ≤ μ) : dualObj q t v μ ≤ expect p v := by
  obtain ⟨⟨hp0, hp1⟩, hpd⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  have h1 : expect p (v - μ) ≤ expect p v := by
    unfold expect
    apply Finset.sum_le_sum
    intro s _
    have := hμ s
    simp only [Pi.sub_apply, Pi.zero_apply] at this ⊢
    nlinarith [hp0 s]
  have h2 : expect p (v - μ) - expect q (v - μ)
      = ∑ s, (p s - q s) * ((v - μ) s - expect q (v - μ)) := by
    have e : ∀ s, (p s - q s) * ((v - μ) s - expect q (v - μ))
        = p s * (v - μ) s - q s * (v - μ) s - expect q (v - μ) * p s + expect q (v - μ) * q s := by
      intro s; ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hp1, hq1]
    unfold expect
    ring
  have hCS : (∑ s, (p s - q s) * ((v - μ) s - expect q (v - μ))) ^ 2
      ≤ (∑ s, (p s - q s) ^ 2 / q s) * (∑ s, q s * ((v - μ) s - expect q (v - μ)) ^ 2) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun s => (p s - q s) / Real.sqrt (q s))
      (fun s => Real.sqrt (q s) * ((v - μ) s - expect q (v - μ)))
    have ea : ∀ s, (p s - q s) / Real.sqrt (q s) * (Real.sqrt (q s) * ((v - μ) s - expect q (v - μ)))
        = (p s - q s) * ((v - μ) s - expect q (v - μ)) := by
      intro s
      have hs := Real.sqrt_pos.2 (hq_pos s)
      field_simp
    have eb : ∀ s, ((p s - q s) / Real.sqrt (q s)) ^ 2 = (p s - q s) ^ 2 / q s := by
      intro s; rw [div_pow, Real.sq_sqrt (hq_pos s).le]
    have ec : ∀ s, (Real.sqrt (q s) * ((v - μ) s - expect q (v - μ))) ^ 2
        = q s * ((v - μ) s - expect q (v - μ)) ^ 2 := by
      intro s; rw [mul_pow, Real.sq_sqrt (hq_pos s).le]
    simp only [ea, eb, ec] at this
    exact this
  have hV : 0 ≤ ∑ s, q s * ((v - μ) s - expect q (v - μ)) ^ 2 :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (hq0 s) (sq_nonneg _))
  have h3 : (∑ s, (p s - q s) * ((v - μ) s - expect q (v - μ))) ^ 2
      ≤ t * variance q (v - μ) := by
    have hd : chiSqDist p q = ∑ s, (p s - q s) ^ 2 / q s := rfl
    have hvar : variance q (v - μ) = ∑ s, q s * ((v - μ) s - expect q (v - μ)) ^ 2 := rfl
    rw [hvar]
    rw [hd] at hpd
    exact hCS.trans (mul_le_mul_of_nonneg_right hpd hV)
  have h4 := Real.abs_le_sqrt h3
  have h5 := neg_abs_le (∑ s, (p s - q s) * ((v - μ) s - expect q (v - μ)))
  unfold dualObj
  linarith

/-- A primal-dual pair with equal values gives the conclusion. -/
lemma l5aux_cert {S : Type*} [Fintype S] (q : S → ℝ) (hq : q ∈ stdSimplex ℝ S)
    (hq_pos : ∀ s, 0 < q s) (t : ℝ) (v p μ : S → ℝ) (hp : p ∈ chiSqSet q t) (hμ : 0 ≤ μ)
    (heq : expect p v = dualObj q t v μ) :
    ∃ val : ℝ,
      IsLeast ((fun p => expect p v) '' chiSqSet q t) val ∧
      IsGreatest ((fun μ => dualObj q t v μ) '' {μ : S → ℝ | 0 ≤ μ}) val := by
  refine ⟨expect p v, ⟨⟨p, hp, rfl⟩, ?_⟩, ⟨⟨μ, hμ, heq.symm⟩, ?_⟩⟩
  · rintro _ ⟨p', hp', rfl⟩
    rw [heq]
    exact l5aux_weak q hq hq_pos t v p' hp' μ hμ
  · rintro _ ⟨μ', hμ', rfl⟩
    exact l5aux_weak q hq hq_pos t v p hp μ' hμ'

/-- The tilted measure `q u / d` lies in the simplex and has χ²-distance `∑ q u² / d² - 1`. -/
lemma l5aux_tilt {S : Type*} [Fintype S] (q : S → ℝ) (hq : q ∈ stdSimplex ℝ S)
    (hq_pos : ∀ s, 0 < q s) (u : S → ℝ) (hu : ∀ s, 0 ≤ u s) (hd : 0 < ∑ s, q s * u s) :
    (fun s => q s * u s / ∑ s, q s * u s) ∈ stdSimplex ℝ S ∧
    chiSqDist (fun s => q s * u s / ∑ s, q s * u s) q
      = (∑ s, q s * u s ^ 2) / (∑ s, q s * u s) ^ 2 - 1 := by
  obtain ⟨hq0, hq1⟩ := hq
  set d := ∑ s, q s * u s with hdd
  refine ⟨⟨fun s => div_nonneg (mul_nonneg (hq0 s) (hu s)) hd.le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div, ← hdd]; exact div_self hd.ne'
  · unfold chiSqDist
    have e : ∀ s, (q s * u s / d - q s) ^ 2 / q s
        = (q s * u s ^ 2) / d ^ 2 - 2 * (q s * u s) / d + q s := by
      intro s
      have := (hq_pos s).ne'
      field_simp
      ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
      ← Finset.mul_sum, ← hdd, hq1]
    field_simp
    ring

end RobustDP.ChiSquare

open RobustDP.ChiSquare in
theorem solution {S : Type*} [Fintype S] (q : S → ℝ)
    (hq : q ∈ stdSimplex ℝ S) (hq_pos : ∀ s, 0 < q s) (t : ℝ) (ht : 0 ≤ t) (v : S → ℝ) :
    ∃ val : ℝ,
      IsLeast ((fun p => expect p v) '' chiSqSet q t) val ∧
      IsGreatest ((fun μ => dualObj q t v μ) '' {μ : S → ℝ | 0 ≤ μ}) val := by
  have hq0 := hq.1
  have hq1 := hq.2
  -- the case t = 0
  rcases ht.lt_or_eq with htpos | rfl
  swap
  · refine l5aux_cert q hq hq_pos 0 v q 0 ⟨hq, ?_⟩ le_rfl ?_
    · unfold chiSqDist; simp
    · unfold dualObj; simp
  have hne : (Finset.univ : Finset S).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hq1
    exact zero_ne_one hq1
  set m := Finset.univ.inf' hne v with hm
  obtain ⟨s0, -, hs0⟩ := Finset.exists_mem_eq_inf' hne v
  have hmle : ∀ s, m ≤ v s := fun s => Finset.inf'_le _ (Finset.mem_univ s)
  set κ0 := Finset.univ.inf' hne (fun s => if v s = m then m + 1 else v s) with hκ0
  have hκ0m : m < κ0 := by
    rw [hκ0, Finset.lt_inf'_iff]
    intro s _
    split_ifs with h
    · linarith
    · exact lt_of_le_of_ne (hmle s) (Ne.symm h)
  have hκ0v : ∀ s, v s < κ0 → v s = m := by
    intro s hs
    by_contra h
    have := Finset.inf'_le (fun s => if v s = m then m + 1 else v s) (Finset.mem_univ s)
    rw [← hκ0, if_neg h] at this
    linarith
  -- the function whose zero gives the multiplier
  set H : ℝ → ℝ := fun κ => (∑ s, q s * (max (κ - v s) 0) ^ 2)
      - (1 + t) * (∑ s, q s * max (κ - v s) 0) ^ 2 with hH
  have dpos : ∀ κ, m < κ → 0 < ∑ s, q s * max (κ - v s) 0 := by
    intro κ hκ
    apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun s => q s * max (κ - v s) 0)
      (fun s _ => mul_nonneg (hq0 s) (le_max_right _ _)) (Finset.mem_univ s0))
    apply mul_pos (hq_pos s0)
    have hs0' : m = v s0 := hs0
    rw [hs0'] at hκ
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  by_cases hH0 : H κ0 ≤ 0
  · -- inactive constraint: all mass on the minimisers of v
    set u : S → ℝ := fun s => max (κ0 - v s) 0 with hu
    have hu0 : ∀ s, 0 ≤ u s := fun s => le_max_right _ _
    have hd := dpos κ0 hκ0m
    obtain ⟨hsimp, hchi⟩ := l5aux_tilt q hq hq_pos u hu0 hd
    have huv : ∀ s, q s * u s * v s = m * (q s * u s) := by
      intro s
      by_cases h : v s < κ0
      · rw [hκ0v s h]; ring
      · have : u s = 0 := by simp only [hu]; exact max_eq_right (by linarith)
        rw [this]; ring
    refine l5aux_cert q hq hq_pos t v _ (fun s => v s - m) ⟨hsimp, ?_⟩ ?_ ?_
    · rw [hchi]
      have hd2 : 0 < (∑ s, q s * u s) ^ 2 := by positivity
      rw [div_sub_one hd2.ne', div_le_iff₀ hd2]
      have : H κ0 = (∑ s, q s * u s ^ 2) - (1 + t) * (∑ s, q s * u s) ^ 2 := rfl
      nlinarith
    · intro s; simp only [Pi.zero_apply]; linarith [hmle s]
    · unfold expect dualObj variance expect
      have e1 : ∀ s, q s * u s / (∑ s, q s * u s) * v s = m * (q s * u s) / ∑ s, q s * u s := by
        intro s; rw [← huv s]; ring
      have e2 : (v - fun s => v s - m) = fun _ => m := by
        funext s; simp
      simp_rw [e1, e2]
      rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc, div_self hd.ne', ← Finset.sum_mul, hq1]
      simp
  · -- active constraint: find κ with H κ = 0 by the intermediate value theorem
    rw [not_le] at hH0
    set M := Finset.univ.sup' hne v with hM
    have hMge : ∀ s, v s ≤ M := fun s => Finset.le_sup' _ (Finset.mem_univ s)
    set D := M - m with hD
    have hD0 : 0 ≤ D := by have := hmle s0; have := hMge s0; linarith
    set x := (2 * D + D ^ 2 + 1) / t + 1 with hx
    set κ2 := max κ0 M + x with hκ2
    have hx1 : 1 ≤ x := by
      have : 0 ≤ (2 * D + D ^ 2 + 1) / t := by positivity
      linarith
    have htx : 2 * D + D ^ 2 + 1 ≤ t * x := by
      rw [hx, mul_add, mul_div_cancel₀ _ htpos.ne']; linarith
    have hκ2le : κ0 ≤ κ2 := by
      have := le_max_left κ0 M; linarith
    have hH2 : H κ2 ≤ 0 := by
      set y := κ2 - M with hy
      have hyx : x ≤ y := by have := le_max_right κ0 M; linarith
      have hmx : ∀ s, max (κ2 - v s) 0 = κ2 - v s := fun s =>
        max_eq_left (by have := hMge s; linarith)
      have hA : ∑ s, q s * (max (κ2 - v s) 0) ^ 2 ≤ (y + D) ^ 2 := by
        calc ∑ s, q s * (max (κ2 - v s) 0) ^ 2 ≤ ∑ s, q s * (y + D) ^ 2 := by
              apply Finset.sum_le_sum; intro s _
              rw [hmx s]
              apply mul_le_mul_of_nonneg_left _ (hq0 s)
              have := hMge s; have := hmle s
              apply pow_le_pow_left₀ (by linarith) (by linarith)
          _ = (y + D) ^ 2 := by rw [← Finset.sum_mul, hq1, one_mul]
      have hB : y ≤ ∑ s, q s * max (κ2 - v s) 0 := by
        calc y = ∑ s, q s * y := by rw [← Finset.sum_mul, hq1, one_mul]
          _ ≤ ∑ s, q s * max (κ2 - v s) 0 := by
              apply Finset.sum_le_sum; intro s _
              rw [hmx s]
              apply mul_le_mul_of_nonneg_left _ (hq0 s)
              have := hMge s; linarith
      have hy0 : 0 ≤ y := by linarith
      have hB2 : y ^ 2 ≤ (∑ s, q s * max (κ2 - v s) 0) ^ 2 := pow_le_pow_left₀ hy0 hB 2
      have hty : 2 * D + D ^ 2 + 1 ≤ t * y := le_trans htx (mul_le_mul_of_nonneg_left hyx htpos.le)
      have key : (y + D) ^ 2 ≤ (1 + t) * y ^ 2 := by nlinarith
      show (∑ s, q s * (max (κ2 - v s) 0) ^ 2)
        - (1 + t) * (∑ s, q s * max (κ2 - v s) 0) ^ 2 ≤ 0
      nlinarith
    have hcont : ContinuousOn H (Set.Icc κ0 κ2) := by
      apply Continuous.continuousOn
      simp only [hH]
      fun_prop
    obtain ⟨κ, ⟨hκlo, -⟩, hκ⟩ :=
      intermediate_value_Icc' hκ2le hcont ⟨hH2, hH0.le⟩
    have hκm : m < κ := lt_of_lt_of_le hκ0m hκlo
    set u : S → ℝ := fun s => max (κ - v s) 0 with hu
    have hu0 : ∀ s, 0 ≤ u s := fun s => le_max_right _ _
    have hd := dpos κ hκm
    obtain ⟨hsimp, hchi⟩ := l5aux_tilt q hq hq_pos u hu0 hd
    set d := ∑ s, q s * u s with hdd
    have hHk : (∑ s, q s * u s ^ 2) = (1 + t) * d ^ 2 := by
      have : H κ = (∑ s, q s * u s ^ 2) - (1 + t) * d ^ 2 := rfl
      linarith
    have huv : ∀ s, u s * v s = u s * (κ - u s) := by
      intro s
      by_cases h : v s ≤ κ
      · have : u s = κ - v s := max_eq_left (by linarith)
        rw [this]; ring
      · have : u s = 0 := max_eq_right (by linarith)
        rw [this]; ring
    have hw : (v - fun s => max (v s - κ) 0) = fun s => κ - u s := by
      funext s
      simp only [Pi.sub_apply, hu]
      by_cases h : v s ≤ κ
      · rw [max_eq_right (by linarith : v s - κ ≤ 0), max_eq_left (by linarith : 0 ≤ κ - v s)]
        ring
      · rw [max_eq_left (by linarith : 0 ≤ v s - κ), max_eq_right (by linarith : κ - v s ≤ 0)]
        ring
    have hEw : expect q (fun s => κ - u s) = κ - d := by
      unfold expect
      have e : ∀ s, q s * (κ - u s) = κ * q s - q s * u s := fun s => by ring
      simp_rw [e]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hq1]; ring
    have hVw : variance q (fun s => κ - u s) = t * d ^ 2 := by
      unfold variance
      rw [hEw]
      have e : ∀ s, q s * (κ - u s - (κ - d)) ^ 2
          = q s * u s ^ 2 - 2 * d * (q s * u s) + d ^ 2 * q s := fun s => by ring
      simp_rw [e]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hq1, hHk]
      ring
    refine l5aux_cert q hq hq_pos t v _ (fun s => max (v s - κ) 0) ⟨hsimp, ?_⟩ ?_ ?_
    · rw [hchi, hHk]
      have hd2 : 0 < d ^ 2 := by positivity
      rw [mul_div_assoc, div_self hd2.ne']; linarith
    · intro s; exact le_max_right _ _
    · unfold dualObj
      rw [hw, hEw, hVw]
      have hs : Real.sqrt (t * (t * d ^ 2)) = t * d := by
        rw [show t * (t * d ^ 2) = (t * d) ^ 2 by ring]
        exact Real.sqrt_sq (by positivity)
      rw [hs]
      unfold expect
      beta_reduce
      have e : ∀ s, q s * u s / d * v s = (κ * (q s * u s) - q s * u s ^ 2) / d := by
        intro s
        have := huv s
        field_simp
        linear_combination q s * this
      simp_rw [e]
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hdd, hHk]
      field_simp
      ring
