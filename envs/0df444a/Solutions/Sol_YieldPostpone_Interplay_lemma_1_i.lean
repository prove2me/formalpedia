-- Prove2me | solution 1 for YieldPostpone.Interplay.lemma_1_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T04:25:40.850656+00:00
-- url     : https://prove2.me/submissions/78dea6e7-a9ad-494c-b9e0-93fcec68fd2d

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting


open YieldPostpone.Interplay

namespace YP3L1i

/-- the cubic defining `θ₂(α)` -/
def pc (α x : ℝ) : ℝ :=
  -α ^ 3 + α ^ 2 * (5 + α) * x + (16 - 19 * α - 6 * α ^ 2) * x ^ 2 - 25 * (1 - α) * x ^ 3

lemma pc_cont (α : ℝ) : Continuous (pc α) := by unfold pc; fun_prop

lemma theta1_mul (α : ℝ) (hα1 : α < 1) :
    theta1 α * (8 * (1 - α)) = 1 - 4 * α + Real.sqrt (1 + 8 * α) := by
  unfold theta1
  have : (8 * (1 - α)) ≠ 0 := by
    have : 0 < 1 - α := by linarith
    positivity
  exact div_mul_cancel₀ _ this

lemma sqrt_facts (α : ℝ) (hα0 : 0 < α) :
    Real.sqrt (1 + 8 * α) ^ 2 = 1 + 8 * α ∧ 1 < Real.sqrt (1 + 8 * α) := by
  refine ⟨Real.sq_sqrt (by linarith), ?_⟩
  exact (Real.lt_sqrt (by norm_num)).mpr (by linarith)

/-- `p(θ₁) > 0` -/
lemma pc_theta1 (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) : 0 < pc α (theta1 α) := by
  obtain ⟨hr2, hr1⟩ := sqrt_facts α hα0
  set r := Real.sqrt (1 + 8 * α) with hr
  have ht := theta1_mul α hα1
  rw [← hr] at ht
  set t := theta1 α
  have h1α : 0 < 1 - α := by linarith
  set L := 8 * (1 - α) with hL
  have hL0 : 0 < L := by rw [hL]; positivity
  have e1 : pc α t * L ^ 3 = -α ^ 3 * L ^ 3 + α ^ 2 * (5 + α) * (t * L) * L ^ 2 +
      (16 - 19 * α - 6 * α ^ 2) * (t * L) ^ 2 * L - 25 * (1 - α) * (t * L) ^ 3 := by
    unfold pc; ring
  rw [ht] at e1
  have e2 : pc α t * L ^ 3 = 4 * (α - 1) *
      ((64*α^5 - 304*α^4 + 720*α^3 - 868*α^2 + 76*α - 39) +
        (16*α^4 - 32*α^3 - 60*α^2 + 232*α - 39) * r) := by
    rw [e1, hL]
    linear_combination (48*α^3 - 196*α^2 + 95*α + r*(25*α - 25) + 53) * hr2
  have hQ0 : 64*α^5 - 304*α^4 + 720*α^3 - 868*α^2 + 76*α - 39 < 0 := by
    have a1 : α ^ 5 ≤ α ^ 4 := pow_le_pow_of_le_one hα0.le hα1.le (by norm_num)
    have a2 : α ^ 3 ≤ α ^ 2 := pow_le_pow_of_le_one hα0.le hα1.le (by norm_num)
    have a3 : 0 ≤ α ^ 4 := by positivity
    nlinarith [sq_nonneg (α - 1 / 4)]
  have hN : (64*α^5 - 304*α^4 + 720*α^3 - 868*α^2 + 76*α - 39) ^ 2 -
      ((16*α^4 - 32*α^3 - 60*α^2 + 232*α - 39) * r) ^ 2 =
      4096 * α ^ 2 * ((3 - α) * (1 - α) ^ 3) * (α ^ 4 - 4 * α ^ 3 + 11 * α ^ 2 - 8 * α + 13) := by
    rw [mul_pow, hr2]; ring
  have hq4 : 0 < α ^ 4 - 4 * α ^ 3 + 11 * α ^ 2 - 8 * α + 13 := by
    nlinarith [sq_nonneg (α ^ 2 - 2 * α), sq_nonneg (α - 4 / 7)]
  have hNpos : 0 < 4096 * α ^ 2 * ((3 - α) * (1 - α) ^ 3) *
      (α ^ 4 - 4 * α ^ 3 + 11 * α ^ 2 - 8 * α + 13) := by
    have : 0 < 3 - α := by linarith
    positivity
  have hlt : (16*α^4 - 32*α^3 - 60*α^2 + 232*α - 39) * r <
      -(64*α^5 - 304*α^4 + 720*α^3 - 868*α^2 + 76*α - 39) := by
    have hsq : ((16*α^4 - 32*α^3 - 60*α^2 + 232*α - 39) * r) ^ 2 <
        (-(64*α^5 - 304*α^4 + 720*α^3 - 868*α^2 + 76*α - 39)) ^ 2 := by
      rw [neg_sq]; linarith
    exact lt_of_le_of_lt (le_abs_self _) (abs_lt_of_sq_lt_sq hsq (by linarith))
  have : 0 < pc α t * L ^ 3 := by
    rw [e2]
    have : (64*α^5 - 304*α^4 + 720*α^3 - 868*α^2 + 76*α - 39) +
        (16*α^4 - 32*α^3 - 60*α^2 + 232*α - 39) * r < 0 := by linarith
    nlinarith
  exact pos_of_mul_pos_left this (by positivity) |> fun h => by
    by_contra hc; push Not at hc
    have : pc α t * L ^ 3 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by positivity)
    linarith

/-- the inflection point of `p` lies below `θ₁` -/
lemma infl (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    16 - 19 * α - 6 * α ^ 2 ≤ 75 * (1 - α) * theta1 α := by
  obtain ⟨hr2, hr1⟩ := sqrt_facts α hα0
  have ht := theta1_mul α hα1
  set r := Real.sqrt (1 + 8 * α) with hr
  have hX : 53 + 148 * α - 48 * α ^ 2 ≤ 75 * r := by
    have h0 : 0 ≤ 53 + 148 * α - 48 * α ^ 2 := by nlinarith
    have : (53 + 148 * α - 48 * α ^ 2) ^ 2 ≤ (75 * r) ^ 2 := by
      rw [mul_pow, hr2]; nlinarith [sq_nonneg α, mul_pos hα0 hα0]
    exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).mp this
  have : 75 * (1 - α) * theta1 α = 75 * (1 - 4 * α + r) / 8 := by
    rw [← ht]; ring
  rw [this]; nlinarith

lemma pc_neg_ge1 (α x : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hx : 1 ≤ x) : pc α x < 0 := by
  have e : pc α x = -(3 - α) ^ 2 + (α ^ 3 - 7 * α ^ 2 + 37 * α - 43) * (x - 1) +
      (-59 + 56 * α - 6 * α ^ 2) * (x - 1) ^ 2 - 25 * (1 - α) * (x - 1) ^ 3 := by
    unfold pc; ring
  rw [e]
  have ht : 0 ≤ x - 1 := by linarith
  have c1 : α ^ 3 - 7 * α ^ 2 + 37 * α - 43 < 0 := by nlinarith [pow_pos hα0 3]
  have c2 : -59 + 56 * α - 6 * α ^ 2 < 0 := by nlinarith
  have h1 : (α ^ 3 - 7 * α ^ 2 + 37 * α - 43) * (x - 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg c1.le ht
  have h2 : (-59 + 56 * α - 6 * α ^ 2) * (x - 1) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg c2.le (by positivity)
  have h3 : 0 ≤ 25 * (1 - α) * (x - 1) ^ 3 := by
    have : 0 < 1 - α := by linarith
    positivity
  have h4 : 0 < (3 - α) ^ 2 := by
    have : 0 < 3 - α := by linarith
    positivity
  linarith

lemma theta1_lt_one (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) : theta1 α < 1 := by
  obtain ⟨hr2, hr1⟩ := sqrt_facts α hα0
  have ht := theta1_mul α hα1
  have h1α : 0 < 1 - α := by linarith
  have hr7 : Real.sqrt (1 + 8 * α) < 7 - 4 * α := by
    rw [show 7 - 4 * α = Real.sqrt ((7 - 4 * α) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_lt_sqrt (by linarith) (by nlinarith)
  by_contra h; push Not at h
  have := mul_le_mul_of_nonneg_right h (by positivity : (0:ℝ) ≤ 8 * (1 - α))
  linarith

lemma theta1_pos (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) : 0 < theta1 α := by
  obtain ⟨hr2, hr1⟩ := sqrt_facts α hα0
  unfold theta1
  apply div_pos _ (by linarith)
  -- `√(1+8α) > 4α - 1`
  rcases le_or_gt (4 * α - 1) 0 with h | h
  · linarith
  · have : 4 * α - 1 < Real.sqrt (1 + 8 * α) := by
      rw [show 4 * α - 1 = Real.sqrt ((4 * α - 1) ^ 2) by rw [Real.sqrt_sq h.le]]
      exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
    linarith

/-- the properties of `θ₂` -/
lemma theta2_props (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    pc α (theta2 α) = 0 ∧ theta1 α < theta2 α ∧ ∀ x, theta2 α < x → pc α x < 0 := by
  have hset : theta2 α = sSup {x : ℝ | pc α x = 0} := rfl
  have hcl : IsClosed {x : ℝ | pc α x = 0} := isClosed_eq (pc_cont α) continuous_const
  have hbdd : BddAbove {x : ℝ | pc α x = 0} := by
    refine ⟨1, fun x hx => ?_⟩
    by_contra h; push Not at h
    have := pc_neg_ge1 α x hα0 hα1 h.le
    exact absurd hx (by simp only [Set.mem_setOf_eq]; linarith)
  have h1 := pc_theta1 α hα0 hα1
  have h1l := theta1_lt_one α hα0 hα1
  have hpc1 : pc α 1 < 0 := pc_neg_ge1 α 1 hα0 hα1 le_rfl
  obtain ⟨ρ, hρ, hρ0⟩ : ∃ ρ ∈ Set.Icc (theta1 α) 1, pc α ρ = 0 := by
    have := intermediate_value_Icc' h1l.le (pc_cont α).continuousOn
    exact this ⟨hpc1.le, h1.le⟩
  have hne : ({x : ℝ | pc α x = 0}).Nonempty := ⟨ρ, hρ0⟩
  have hmem := hcl.csSup_mem hne hbdd
  rw [← hset] at hmem
  have hρθ : theta1 α < ρ := by
    rcases hρ.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hρ0; linarith
  have hρle : ρ ≤ theta2 α := by rw [hset]; exact le_csSup hbdd hρ0
  refine ⟨hmem, lt_of_lt_of_le hρθ hρle, fun x hx => ?_⟩
  by_contra hc; push Not at hc
  rcases le_or_gt 1 x with hx1 | hx1
  · have := pc_neg_ge1 α x hα0 hα1 hx1; linarith
  · obtain ⟨y, hy, hy0⟩ : ∃ y ∈ Set.Icc x 1, pc α y = 0 := by
      have := intermediate_value_Icc' hx1.le (pc_cont α).continuousOn
      exact this ⟨hpc1.le, hc⟩
    have : y ≤ theta2 α := by rw [hset]; exact le_csSup hbdd hy0
    linarith [hy.1]

/-- `p > 0` strictly between `θ₁` and `θ₂` -/
lemma pc_pos_between (α x : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (h1 : theta1 α < x)
    (h2 : x < theta2 α) : 0 < pc α x := by
  obtain ⟨hz, h12, -⟩ := theta2_props α hα0 hα1
  have hp1 := pc_theta1 α hα0 hα1
  have hin := infl α hα0 hα1
  set t1 := theta1 α
  set t2 := theta2 α
  have key : pc α x * (t2 - t1) = pc α t1 * (t2 - x) + pc α t2 * (x - t1) +
      (t2 - t1) * (x - t1) * (x - t2) *
        (-25 * (1 - α) * (x + t1 + t2) + (16 - 19 * α - 6 * α ^ 2)) := by
    unfold pc; ring
  rw [hz, zero_mul, add_zero] at key
  have hlin : -25 * (1 - α) * (x + t1 + t2) + (16 - 19 * α - 6 * α ^ 2) ≤ 0 := by
    have : 3 * t1 < x + t1 + t2 := by linarith
    have h1α : 0 < 1 - α := by linarith
    nlinarith
  have hprod : (t2 - t1) * (x - t1) * (x - t2) < 0 := by
    have : 0 < (t2 - t1) * (x - t1) := mul_pos (by linarith) (by linarith)
    exact mul_neg_of_pos_of_neg this (by linarith)
  have : 0 < pc α x * (t2 - t1) := by
    rw [key]
    have : 0 ≤ (t2 - t1) * (x - t1) * (x - t2) *
        (-25 * (1 - α) * (x + t1 + t2) + (16 - 19 * α - 6 * α ^ 2)) :=
      mul_nonneg_of_nonpos_of_nonpos hprod.le hlin
    have : 0 < pc α t1 * (t2 - x) := mul_pos hp1 (by linarith)
    linarith
  by_contra hc; push Not at hc
  have : pc α x * (t2 - t1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by linarith)
  linarith

end YP3L1i


open YieldPostpone.Interplay

namespace YP3L1i

noncomputable def Kq (P : Params) : ℝ := 4 * P.b * μ P * (P.a * P.α - P.b * what P)
noncomputable def Aq (P : Params) : ℝ := P.α ^ 2 * P.b ^ 2
noncomputable def Bq (P : Params) : ℝ := -2 * P.α ^ 2 * P.a * P.b * μ P + Kq P
noncomputable def Cq (P : Params) : ℝ := P.α ^ 2 * P.a ^ 2 * μ P ^ 2 - Kq P * what P

lemma cOA2_eq (P : Params) :
    cOA2 P = (-Bq P + Real.sqrt (Bq P ^ 2 - 4 * Aq P * Cq P)) / (2 * Aq P) := rfl

lemma qr1 (A B C c : ℝ) (hA : 0 < A) (h : A * c ^ 2 + B * c + C < 0) :
    c < (-B + Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A) := by
  have hD : (2 * A * c + B) ^ 2 < B ^ 2 - 4 * A * C := by nlinarith
  have h1 : 2 * A * c + B < Real.sqrt (B ^ 2 - 4 * A * C) := by
    calc 2 * A * c + B ≤ |2 * A * c + B| := le_abs_self _
      _ = Real.sqrt ((2 * A * c + B) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ < Real.sqrt (B ^ 2 - 4 * A * C) := Real.sqrt_lt_sqrt (sq_nonneg _) hD
  rw [lt_div_iff₀ (by positivity)]; linarith

lemma qr2 (A B C : ℝ) (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    (-B + Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A) ≤ 0 := by
  have : Real.sqrt (B ^ 2 - 4 * A * C) ≤ B := by
    calc Real.sqrt (B ^ 2 - 4 * A * C) ≤ Real.sqrt (B ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = B := Real.sqrt_sq hB
  apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

lemma qr3 (A B C : ℝ) (hA : 0 < A) (hC : C < 0) :
    0 < (-B + Real.sqrt (B ^ 2 - 4 * A * C)) / (2 * A) := by
  have : B < Real.sqrt (B ^ 2 - 4 * A * C) := by
    calc B ≤ |B| := le_abs_self _
      _ = Real.sqrt (B ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ < Real.sqrt (B ^ 2 - 4 * A * C) := Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
  apply div_pos (by linarith) (by positivity)

/-- the algebra of the OA thresholds, with `s = √μ` -/
lemma oa_alg (P : Params) (hP : P.Valid) :
    Aq P * cOA1 P ^ 2 + Bq P * cOA1 P + Cq P < 0 ∧
    Cq P * (P.α + P.θ) ^ 2 = P.a ^ 2 * P.α ^ 2 * μ P * Real.sqrt (μ P) *
      (Real.sqrt (μ P) * ((P.α - P.θ) ^ 2 + 4 * P.θ ^ 2) -
        4 * P.θ * (P.α + P.θ - 2 * P.α * P.θ)) ∧
    cOA1 P * (P.b * (P.α + P.θ)) =
      P.a * P.α * (μ P - P.α * P.θ - 2 * P.θ * Real.sqrt (μ P)) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  set s := Real.sqrt (μ P) with hsdef
  have hs : s ^ 2 = μ P := Real.sq_sqrt hμ0.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hμ0
  have hαs : P.α < s := by
    rw [hsdef]; apply Real.lt_sqrt_of_sq_lt; rw [hμ]; nlinarith [mul_pos hα0 h1θ]
  have hαθ : 0 < P.α + P.θ := by linarith
  have hW : P.b * what P * (P.α + P.θ) = P.a * P.α * (μ P - P.θ * s) := by
    unfold what; rw [← hsdef]; field_simp
  have hc1 : cOA1 P * (P.b * (P.α + P.θ)) =
      P.a * P.α * (μ P - P.α * P.θ - 2 * P.θ * s) := by
    unfold cOA1; rw [← hsdef]; field_simp
  have hbc1 : P.b * cOA1 P = 2 * (P.b * what P) - P.a * P.α := by
    have : (P.b * cOA1 P) * (P.α + P.θ) = (2 * (P.b * what P) - P.a * P.α) * (P.α + P.θ) := by
      have e : (2 * (P.b * what P) - P.a * P.α) * (P.α + P.θ) =
          2 * (P.b * what P * (P.α + P.θ)) - P.a * P.α * (P.α + P.θ) := by ring
      rw [e, hW]
      have e2 : P.b * cOA1 P * (P.α + P.θ) = cOA1 P * (P.b * (P.α + P.θ)) := by ring
      rw [e2, hc1, hμ]; ring
    exact mul_right_cancel₀ hαθ.ne' this
  set W := P.b * what P with hWdef
  have E1 : (P.a * μ P + P.a * P.α - 2 * W) * (P.α + P.θ) = P.a * P.θ * (s + P.α) ^ 2 := by
    have e : (P.a * μ P + P.a * P.α - 2 * W) * (P.α + P.θ) =
        P.a * μ P * (P.α + P.θ) + P.a * P.α * (P.α + P.θ) - 2 * (W * (P.α + P.θ)) := by ring
    rw [e, hW]
    linear_combination (-(P.a * P.θ)) * hs - (P.a * P.α) * hμ
  have E2 : (P.a * P.α - W) * (P.α + P.θ) = P.a * P.α * P.θ * (P.α + s) := by
    have e : (P.a * P.α - W) * (P.α + P.θ) = P.a * P.α * (P.α + P.θ) - W * (P.α + P.θ) := by ring
    rw [e, hW, hμ]; ring
  have hK : Kq P = 4 * μ P * (P.a * P.α - W) * P.b := by unfold Kq; rw [hWdef]; ring
  refine ⟨?_, ?_, hc1⟩
  · have hh : Aq P * cOA1 P ^ 2 + Bq P * cOA1 P + Cq P =
        P.α ^ 2 * (P.a * μ P - P.b * cOA1 P) ^ 2 - 4 * μ P * (P.a * P.α - W) * (W - P.b * cOA1 P) := by
      unfold Aq Bq Cq; rw [hK, hWdef]; ring
    rw [hh, hbc1]
    have e3 : W - (2 * W - P.a * P.α) = P.a * P.α - W := by ring
    have e4 : P.a * μ P - (2 * W - P.a * P.α) = P.a * μ P + P.a * P.α - 2 * W := by ring
    rw [e3, e4]
    have hpos : 0 < (P.α + P.θ) ^ 2 := by positivity
    have key : (P.α ^ 2 * (P.a * μ P + P.a * P.α - 2 * W) ^ 2 - 4 * μ P * (P.a * P.α - W) * (P.a * P.α - W)) *
        (P.α + P.θ) ^ 2 = P.a ^ 2 * P.α ^ 2 * P.θ ^ 2 * (s + P.α) ^ 2 * ((P.α - s) * (P.α + 3 * s)) := by
      have : (P.α ^ 2 * (P.a * μ P + P.a * P.α - 2 * W) ^ 2 - 4 * μ P * (P.a * P.α - W) * (P.a * P.α - W)) *
          (P.α + P.θ) ^ 2 = P.α ^ 2 * ((P.a * μ P + P.a * P.α - 2 * W) * (P.α + P.θ)) ^ 2 -
            4 * μ P * ((P.a * P.α - W) * (P.α + P.θ)) ^ 2 := by ring
      rw [this, E1, E2, ← hs]; ring
    have hneg : P.a ^ 2 * P.α ^ 2 * P.θ ^ 2 * (s + P.α) ^ 2 * ((P.α - s) * (P.α + 3 * s)) < 0 := by
      apply mul_neg_of_pos_of_neg (by positivity)
      exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    by_contra hc; push Not at hc
    have := mul_nonneg hc hpos.le
    linarith
  · have hC : Cq P = P.α ^ 2 * P.a ^ 2 * μ P ^ 2 - 4 * μ P * (P.a * P.α - W) * W := by
      unfold Cq; rw [hK, hWdef]; ring
    rw [hC]
    have : (P.α ^ 2 * P.a ^ 2 * μ P ^ 2 - 4 * μ P * (P.a * P.α - W) * W) * (P.α + P.θ) ^ 2 =
        P.α ^ 2 * P.a ^ 2 * μ P ^ 2 * (P.α + P.θ) ^ 2 -
          4 * μ P * ((P.a * P.α - W) * (P.α + P.θ)) * (W * (P.α + P.θ)) := by ring
    rw [this, E2, hW, ← hs]
    have hs' : s ^ 2 = P.α * (1 - P.θ) + P.θ := by rw [hs, hμ]
    linear_combination (-4 * P.a ^ 2 * P.α ^ 2 * s ^ 3 * P.θ) * hs'

end YP3L1i


open YieldPostpone.Interplay

namespace YP3L1i

lemma F_sign (P : Params) (hP : P.Valid) :
    (pc P.α P.θ < 0 → 0 < Real.sqrt (μ P) * ((P.α - P.θ) ^ 2 + 4 * P.θ ^ 2) -
        4 * P.θ * (P.α + P.θ - 2 * P.α * P.θ)) ∧
    (0 < pc P.α P.θ → Real.sqrt (μ P) * ((P.α - P.θ) ^ 2 + 4 * P.θ ^ 2) -
        4 * P.θ * (P.α + P.θ - 2 * P.α * P.θ) < 0) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have h1θ : 0 < 1 - P.θ := by linarith
  have h1α : 0 < 1 - P.α := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  set s := Real.sqrt (μ P) with hsdef
  have hs : s ^ 2 = μ P := Real.sq_sqrt hμ0.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hμ0
  set X := (P.α - P.θ) ^ 2 + 4 * P.θ ^ 2 with hX
  set Y := 4 * P.θ * (P.α + P.θ - 2 * P.α * P.θ) with hY
  have hX0 : 0 < X := by rw [hX]; positivity
  have hY0 : 0 < Y := by
    rw [hY]; have : 0 < P.α + P.θ - 2 * P.α * P.θ := by nlinarith [mul_pos hα0 h1θ, mul_pos hθ0 h1α]
    positivity
  have key : (s * X) ^ 2 - Y ^ 2 = -(P.α + P.θ) ^ 2 * pc P.α P.θ := by
    rw [mul_pow, hs, hμ, hX, hY]; unfold pc; ring
  have hsX : 0 < s * X := mul_pos hs0 hX0
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : Y ^ 2 < (s * X) ^ 2 := by
      have : 0 < -(P.α + P.θ) ^ 2 * pc P.α P.θ := by
        have : 0 < (P.α + P.θ) ^ 2 := by positivity
        nlinarith
      linarith
    have := abs_lt_of_sq_lt_sq this hsX.le
    linarith [le_abs_self Y]
  · have : (s * X) ^ 2 < Y ^ 2 := by
      have : -(P.α + P.θ) ^ 2 * pc P.α P.θ < 0 := by
        have : 0 < (P.α + P.θ) ^ 2 := by positivity
        nlinarith
      linarith
    have := abs_lt_of_sq_lt_sq this hY0.le
    linarith [le_abs_self (s * X)]

lemma cOA1_sign (P : Params) (hP : P.Valid) :
    (P.θ < theta1 P.α → 0 < cOA1 P) ∧ (theta1 P.α < P.θ → cOA1 P < 0) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have h1α : 0 < 1 - P.α := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  obtain ⟨-, -, hc1⟩ := oa_alg P hP
  set s := Real.sqrt (μ P) with hsdef
  have hs : s ^ 2 = μ P := Real.sq_sqrt hμ0.le
  have hs0 : 0 < s := Real.sqrt_pos.mpr hμ0
  obtain ⟨hr2, hr1⟩ := sqrt_facts P.α hα0
  have ht := theta1_mul P.α hα1
  set r := Real.sqrt (1 + 8 * P.α) with hr
  have hD1 : 0 < μ P - P.α * P.θ := by rw [hμ]; nlinarith [mul_pos hα0 h1θ, mul_pos hθ0 h1α]
  have hG : (μ P - P.α * P.θ) ^ 2 - (2 * P.θ * s) ^ 2 =
      -(P.α + P.θ) * ((8 * (1 - P.α) * P.θ - (1 - 4 * P.α)) ^ 2 - r ^ 2) / (16 * (1 - P.α)) := by
    rw [hr2, mul_pow, hs, hμ]; field_simp; ring
  have hden : 0 < P.b * (P.α + P.θ) := by positivity
  have hupr : 0 < 8 * (1 - P.α) * P.θ - (1 - 4 * P.α) + r := by
    have : 0 < 8 * (1 - P.α) * P.θ := by positivity
    linarith
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hu : 8 * (1 - P.α) * P.θ - (1 - 4 * P.α) < r := by
      have := mul_lt_mul_of_pos_right h (by positivity : (0:ℝ) < 8 * (1 - P.α))
      linarith
    have hsq : (8 * (1 - P.α) * P.θ - (1 - 4 * P.α)) ^ 2 - r ^ 2 < 0 := by
      have : (8 * (1 - P.α) * P.θ - (1 - 4 * P.α)) ^ 2 - r ^ 2 =
          (8 * (1 - P.α) * P.θ - (1 - 4 * P.α) - r) * (8 * (1 - P.α) * P.θ - (1 - 4 * P.α) + r) := by ring
      rw [this]; exact mul_neg_of_neg_of_pos (by linarith) hupr
    have : (2 * P.θ * s) ^ 2 < (μ P - P.α * P.θ) ^ 2 := by
      have : 0 < -(P.α + P.θ) * ((8 * (1 - P.α) * P.θ - (1 - 4 * P.α)) ^ 2 - r ^ 2) /
          (16 * (1 - P.α)) := by
        apply div_pos _ (by positivity)
        have : 0 < P.α + P.θ := by linarith
        nlinarith
      linarith
    have h2 := abs_lt_of_sq_lt_sq this hD1.le
    have h3 : 2 * P.θ * s < μ P - P.α * P.θ := lt_of_le_of_lt (le_abs_self _) h2
    have : 0 < cOA1 P * (P.b * (P.α + P.θ)) := by
      rw [hc1]; apply mul_pos (by positivity); linarith
    exact pos_of_mul_pos_left this hden.le
  · have hu : r < 8 * (1 - P.α) * P.θ - (1 - 4 * P.α) := by
      have := mul_lt_mul_of_pos_right h (by positivity : (0:ℝ) < 8 * (1 - P.α))
      linarith
    have hsq : 0 < (8 * (1 - P.α) * P.θ - (1 - 4 * P.α)) ^ 2 - r ^ 2 := by
      have : (8 * (1 - P.α) * P.θ - (1 - 4 * P.α)) ^ 2 - r ^ 2 =
          (8 * (1 - P.α) * P.θ - (1 - 4 * P.α) - r) * (8 * (1 - P.α) * P.θ - (1 - 4 * P.α) + r) := by ring
      rw [this]; exact mul_pos (by linarith) hupr
    have : (μ P - P.α * P.θ) ^ 2 < (2 * P.θ * s) ^ 2 := by
      have : -(P.α + P.θ) * ((8 * (1 - P.α) * P.θ - (1 - 4 * P.α)) ^ 2 - r ^ 2) /
          (16 * (1 - P.α)) < 0 := by
        apply div_neg_of_neg_of_pos _ (by positivity)
        have : 0 < P.α + P.θ := by linarith
        nlinarith
      linarith
    have h2 := abs_lt_of_sq_lt_sq this (by positivity)
    have h3 : μ P - P.α * P.θ < 2 * P.θ * s := lt_of_le_of_lt (le_abs_self _) h2
    have : cOA1 P * (P.b * (P.α + P.θ)) < 0 := by
      rw [hc1]; apply mul_neg_of_pos_of_neg (by positivity); linarith
    by_contra hc; push Not at hc
    have := mul_nonneg hc hden.le
    linarith

end YP3L1i

open YP3L1i in
theorem solution (P : Params) (hP : P.Valid) :
    (H1 P.α P.θ → 0 < cOA1 P ∧ cOA1 P < cOA2 P) ∧
    (H2 P.α P.θ → cOA1 P ≤ 0 ∧ 0 < cOA2 P) ∧
    (H3 P.α P.θ → cOA2 P ≤ 0) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  obtain ⟨hh1, hC, -⟩ := oa_alg P hP
  have hA : 0 < Aq P := by unfold Aq; positivity
  have hlt : cOA1 P < cOA2 P := by rw [cOA2_eq]; exact qr1 _ _ _ _ hA hh1
  obtain ⟨hs1, hs2⟩ := cOA1_sign P hP
  obtain ⟨hF1, hF2⟩ := F_sign P hP
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by
    rw [hμ]; have : 0 < 1 - P.θ := by linarith
    positivity
  have hsq0 : 0 < Real.sqrt (μ P) := Real.sqrt_pos.mpr hμ0
  have hfac : 0 < P.a ^ 2 * P.α ^ 2 * μ P * Real.sqrt (μ P) := by positivity
  have hαθ2 : 0 < (P.α + P.θ) ^ 2 := by positivity
  obtain ⟨-, h12, hneg⟩ := theta2_props P.α hα0 hα1
  refine ⟨fun h => ⟨hs1 h.2, hlt⟩, fun h => ⟨(hs2 h.1).le, ?_⟩, fun h => ?_⟩
  · have hp := pc_pos_between P.α P.θ hα0 hα1 h.1 h.2
    have hF := hF2 hp
    have hCneg : Cq P < 0 := by
      have : Cq P * (P.α + P.θ) ^ 2 < 0 := by rw [hC]; exact mul_neg_of_pos_of_neg hfac hF
      by_contra hc; push Not at hc
      have := mul_nonneg hc hαθ2.le
      linarith
    rw [cOA2_eq]; exact qr3 _ _ _ hA hCneg
  · have hp := hneg P.θ h.1
    have hF := hF1 hp
    have hCpos : 0 < Cq P := by
      have : 0 < Cq P * (P.α + P.θ) ^ 2 := by rw [hC]; exact mul_pos hfac hF
      exact pos_of_mul_pos_left this hαθ2.le
    have hc1 : cOA1 P < 0 := hs2 (lt_trans h12 h.1)
    have hB : 0 < Bq P := by
      have h3 : cOA1 P * (Aq P * cOA1 P + Bq P) < 0 := by nlinarith
      have h4 : 0 < Aq P * cOA1 P + Bq P := by
        by_contra hc; push Not at hc
        have := mul_nonneg_of_nonpos_of_nonpos hc1.le hc
        linarith
      nlinarith
    rw [cOA2_eq]; exact qr2 _ _ _ hA hB.le hCpos.le
