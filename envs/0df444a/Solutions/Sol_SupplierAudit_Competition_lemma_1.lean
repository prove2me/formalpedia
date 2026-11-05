-- Prove2me | solution 1 for SupplierAudit.Competition.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T03:48:38.583598+00:00
-- url     : https://prove2.me/submissions/8e0ee273-eb02-4ed4-8b8b-10f8b136fee7

import Mathlib
import Definitions.Def_SupplierAudit_Competition_Model

namespace SupplierAudit.Competition.P2Sol
open SupplierAudit.Competition Set

variable (P : Params)

lemma Qpos : 0 < 4 - P.β ^ 2 := by nlinarith [P.hβ0, P.hβ1]

lemma Xpos : 0 < P.r * (1 - P.e) := mul_pos P.hr0 (by linarith [P.he1])

lemma Xlt1 : P.r * (1 - P.e) < 1 := by
  have := P.he0; have := P.hr1; have := P.hr0
  nlinarith

lemma s2q_eq (n m : ℕ) : stage2q P n m =
    (2 * (intercept P n - unitCost P n) - P.β * (intercept P m - unitCost P m)) / (4 - P.β ^ 2) :=
  rfl

lemma m0 : intercept P 0 - unitCost P 0 = P.α - 2 * P.w := by
  simp [intercept, unitCost]
lemma m1 : intercept P 1 - unitCost P 1 = P.α - P.dM - P.w - P.wh := by
  simp [intercept, unitCost]; ring
lemma m2 : intercept P 2 - unitCost P 2 = P.α - P.dM - 2 * P.wh := by
  simp [intercept, unitCost]

/-- Expansion of the expected profit over the eight outcomes. -/
lemma exp_eq (K e11 e1c e22 e2c : ℝ) : expProfit₁ P K e11 e1c e22 e2c =
    (1 - lamI P e11) * (1 - lamC P e1c e2c) * (1 - lamI P e22) * stage2Profit P 0 0
    + (1 - lamI P e11) * (1 - lamC P e1c e2c) * lamI P e22 * stage2Profit P 0 1
    + lamI P e11 * (1 - lamC P e1c e2c) * (1 - lamI P e22) * stage2Profit P 1 0
    + lamI P e11 * (1 - lamC P e1c e2c) * lamI P e22 * stage2Profit P 1 1
    + (1 - lamI P e11) * lamC P e1c e2c * (1 - lamI P e22) * stage2Profit P 1 1
    + (1 - lamI P e11) * lamC P e1c e2c * lamI P e22 * stage2Profit P 1 2
    + lamI P e11 * lamC P e1c e2c * (1 - lamI P e22) * stage2Profit P 2 1
    + lamI P e11 * lamC P e1c e2c * lamI P e22 * stage2Profit P 2 2
    - auditCost P K e11 - auditCost P K e1c := by
  simp only [expProfit₁, Fintype.sum_prod_type, Fintype.sum_bool, Bool.toNat_true,
    Bool.toNat_false, if_true]
  norm_num
  ring

lemma tq00 : stage2q P 0 0 = (P.α - 2 * P.w) / (2 + P.β) := by
  have hQ := (Qpos P).ne'
  have h2 : (2 + P.β) ≠ 0 := by linarith [P.hβ0]
  rw [s2q_eq, m0]; field_simp; ring
lemma tq01 : stage2q P 0 1 =
    P.α / (2 + P.β) + (P.β * P.dM - (4 - P.β) * P.w + P.β * P.wh) / (4 - P.β ^ 2) := by
  have hQ := (Qpos P).ne'
  have h2 : (2 + P.β) ≠ 0 := by linarith [P.hβ0]
  rw [s2q_eq, m0, m1]; field_simp; ring
lemma tq10 : stage2q P 1 0 =
    P.α / (2 + P.β) - (2 * P.dM + 2 * (1 - P.β) * P.w + 2 * P.wh) / (4 - P.β ^ 2) := by
  have hQ := (Qpos P).ne'
  have h2 : (2 + P.β) ≠ 0 := by linarith [P.hβ0]
  rw [s2q_eq, m0, m1]; field_simp; ring
lemma tq11 : stage2q P 1 1 = (P.α - P.dM - P.w - P.wh) / (2 + P.β) := by
  have hQ := (Qpos P).ne'
  have h2 : (2 + P.β) ≠ 0 := by linarith [P.hβ0]
  rw [s2q_eq, m1]; field_simp; ring
lemma tq12 : stage2q P 1 2 =
    (P.α - P.dM) / (2 + P.β) - (2 * P.w + 2 * (1 - P.β) * P.wh) / (4 - P.β ^ 2) := by
  have hQ := (Qpos P).ne'
  have h2 : (2 + P.β) ≠ 0 := by linarith [P.hβ0]
  rw [s2q_eq, m1, m2]; field_simp; ring
lemma tq21 : stage2q P 2 1 =
    (P.α - P.dM) / (2 + P.β) - ((4 - P.β) * P.wh - P.β * P.w) / (4 - P.β ^ 2) := by
  have hQ := (Qpos P).ne'
  have h2 : (2 + P.β) ≠ 0 := by linarith [P.hβ0]
  rw [s2q_eq, m1, m2]; field_simp; ring
lemma tq22 : stage2q P 2 2 = (P.α - P.dM - 2 * P.wh) / (2 + P.β) := by
  have hQ := (Qpos P).ne'
  have h2 : (2 + P.β) ≠ 0 := by linarith [P.hβ0]
  rw [s2q_eq, m2]; field_simp; ring

lemma br_eq (y : ℝ) : bestResp P y =
    P.r * (1 - P.e) * (1 - P.r * (1 - P.e)) * (1 - P.r * (1 - P.e) * (1 - y)) / P.a *
        (stage2Profit P 0 0 - stage2Profit P 1 0)
      + P.r * (1 - P.e) * (1 - P.r * (1 - P.e)) * (P.r * (1 - P.e) * (1 - y)) / P.a *
        (stage2Profit P 0 1 - stage2Profit P 1 1)
      + (P.r * (1 - P.e)) ^ 2 * (1 - P.r * (1 - P.e) * (1 - y)) / P.a *
        (stage2Profit P 1 1 - stage2Profit P 2 1)
      + (P.r * (1 - P.e)) ^ 2 * (P.r * (1 - P.e) * (1 - y)) / P.a *
        (stage2Profit P 1 2 - stage2Profit P 2 2) := by
  simp only [bestResp, stage2Profit, tq00, tq01, tq10, tq11, tq12, tq21, tq22]

/-- Profit with each buyer on his independent supplier: auditing gain. -/
lemma gain (K x y : ℝ) : expProfit₁ P K x 0 y 0 =
    expProfit₁ P K 0 0 y 0 + P.a * bestResp P y * x - P.a / 2 * x ^ 2
      - (if 0 < x then K else 0) := by
  have ha := P.ha.ne'
  rw [exp_eq, exp_eq, br_eq]
  simp only [lamI, lamC, auditCost, lt_irrefl, if_false]
  field_simp
  ring

/-- stage-2 quantity bounds. -/
lemma qpos10 : 0 < stage2q P 1 0 := by
  rw [s2q_eq, m0, m1]; apply div_pos _ (Qpos P)
  have := P.hpos1; linarith
lemma qpos11 : 0 < stage2q P 1 1 := by
  rw [s2q_eq, m1]; apply div_pos _ (Qpos P)
  have := P.hpos3; have := P.hw; have := P.hβ1; nlinarith
lemma qpos21 : 0 < stage2q P 2 1 := by
  rw [s2q_eq, m1, m2]; apply div_pos _ (Qpos P)
  have := P.hpos2; linarith

lemma qlt (n m k l : ℕ) (h : (2 * (intercept P k - unitCost P k) - P.β * (intercept P l - unitCost P l)) <
    (2 * (intercept P n - unitCost P n) - P.β * (intercept P m - unitCost P m))) :
    stage2q P k l < stage2q P n m := by
  rw [s2q_eq, s2q_eq]; exact div_lt_div_of_pos_right h (Qpos P)

lemma qle (n m k l : ℕ) (h : (2 * (intercept P k - unitCost P k) - P.β * (intercept P l - unitCost P l)) ≤
    (2 * (intercept P n - unitCost P n) - P.β * (intercept P m - unitCost P m))) :
    stage2q P k l ≤ stage2q P n m := by
  rw [s2q_eq, s2q_eq]; exact div_le_div_of_nonneg_right h (Qpos P).le

lemma d00_10 : stage2Profit P 1 0 < stage2Profit P 0 0 := by
  unfold stage2Profit
  have h0 := qpos10 P
  have h1 : stage2q P 1 0 < stage2q P 0 0 := by
    apply qlt; rw [m0, m1]; have := P.hdM; have := P.hw; linarith
  nlinarith

lemma d11_10 (hβ : 0 < P.β) : stage2Profit P 1 0 < stage2Profit P 1 1 := by
  unfold stage2Profit
  have h0 := qpos10 P
  have h1 : stage2q P 1 0 < stage2q P 1 1 := by
    apply qlt; rw [m0, m1]; have := P.hdM; have := P.hw; nlinarith
  nlinarith

lemma d01_11 : stage2Profit P 1 1 < stage2Profit P 0 1 := by
  unfold stage2Profit
  have h0 := qpos11 P
  have h1 : stage2q P 1 1 < stage2q P 0 1 := by
    apply qlt; rw [m0, m1]; have := P.hdM; have := P.hw; linarith
  nlinarith

lemma d12_11 : stage2Profit P 1 1 ≤ stage2Profit P 1 2 := by
  unfold stage2Profit
  have h0 := qpos11 P
  have h1 : stage2q P 1 1 ≤ stage2q P 1 2 := by
    apply qle; rw [m1, m2]; have := P.hw; have := P.hβ0; nlinarith
  nlinarith

lemma d11_21 : stage2Profit P 2 1 ≤ stage2Profit P 1 1 := by
  unfold stage2Profit
  have h0 := qpos21 P
  have h1 : stage2q P 2 1 ≤ stage2q P 1 1 := by
    apply qle; rw [m1, m2]; have := P.hw; linarith
  nlinarith


/-- Auditing the common supplier is beaten by auditing the independent one with the same effort,
whatever the rival does. -/
lemma dom (hβ : 0 < P.β) (K z u v : ℝ) (hz : 0 < z) (hu : u ∈ Icc (0:ℝ) 1)
    (hv : v ∈ Icc (0:ℝ) 1) : expProfit₁ P K 0 z u v < expProfit₁ P K z 0 u v := by
  have hX := Xpos P
  have hX1 := Xlt1 P
  set X := P.r * (1 - P.e) with hXdef
  have hA := d00_10 P
  have hB := d11_10 P hβ
  have hC := d01_11 P
  have hD := d12_11 P
  have key : expProfit₁ P K z 0 u v - expProfit₁ P K 0 z u v =
      X * z * ((1 - X * (1 - u)) * (v * (stage2Profit P 0 0 - stage2Profit P 1 0)
          + (1 - v) * (stage2Profit P 1 1 - stage2Profit P 1 0))
        + X * (1 - u) * (v * (stage2Profit P 0 1 - stage2Profit P 1 1)
          + (1 - v) * (stage2Profit P 1 2 - stage2Profit P 1 1))) := by
    rw [exp_eq, exp_eq]
    simp only [lamI, lamC, ← hXdef]
    ring
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hv0, hv1⟩ := hv
  have h1 : 0 < v * (stage2Profit P 0 0 - stage2Profit P 1 0)
      + (1 - v) * (stage2Profit P 1 1 - stage2Profit P 1 0) := by
    rcases hv0.eq_or_lt with h | h
    · subst h; simp; linarith
    · have := mul_pos h (sub_pos.2 hA)
      have := mul_nonneg (sub_nonneg.2 hv1) (sub_pos.2 hB).le
      linarith
  have h2 : 0 ≤ v * (stage2Profit P 0 1 - stage2Profit P 1 1)
      + (1 - v) * (stage2Profit P 1 2 - stage2Profit P 1 1) := by
    have := mul_nonneg hv0 (sub_pos.2 hC).le
    have := mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hD)
    linarith
  have hp : 0 < 1 - X * (1 - u) := by nlinarith
  have hp' : 0 ≤ X * (1 - u) := mul_nonneg hX.le (by linarith)
  have : 0 < X * z * ((1 - X * (1 - u)) * (v * (stage2Profit P 0 0 - stage2Profit P 1 0)
          + (1 - v) * (stage2Profit P 1 1 - stage2Profit P 1 0))
        + X * (1 - u) * (v * (stage2Profit P 0 1 - stage2Profit P 1 1)
          + (1 - v) * (stage2Profit P 1 2 - stage2Profit P 1 1))) :=
    mul_pos (mul_pos hX hz) (add_pos_of_pos_of_nonneg (mul_pos hp h1) (mul_nonneg hp' h2))
  linarith

lemma br_aff (y : ℝ) : bestResp P y = bestResp P 0 + (bestResp P 1 - bestResp P 0) * y := by
  simp only [bestResp]; ring

lemma br1_pos : 0 < bestResp P 1 := by
  have hX := Xpos P
  have hX1 := Xlt1 P
  have ha := P.ha
  have hA := d00_10 P
  have hC := d11_21 P
  have e : bestResp P 1 = P.r * (1 - P.e) * (1 - P.r * (1 - P.e)) / P.a *
      (stage2Profit P 0 0 - stage2Profit P 1 0) +
      (P.r * (1 - P.e)) ^ 2 / P.a * (stage2Profit P 1 1 - stage2Profit P 2 1) := by
    rw [br_eq]; ring
  rw [e]
  exact add_pos_of_pos_of_nonneg
    (mul_pos (div_pos (mul_pos hX (by linarith)) ha) (by linarith))
    (mul_nonneg (div_nonneg (sq_nonneg _) ha.le) (by linarith))

lemma br0_eq : bestResp P 0 = eHatI P := by
  have hQ := (Qpos P).ne'
  have ha := P.ha.ne'
  rw [br_eq]
  simp only [stage2Profit, s2q_eq, m0, m1, m2, eHatI]
  generalize P.r * (1 - P.e) = X
  generalize 4 - P.β ^ 2 = Q at hQ ⊢
  field_simp
  ring

/-- the slope of the best response. -/
lemma slope_eq : bestResp P 1 - bestResp P 0 =
    -(4 * P.β * (P.r * (1 - P.e)) ^ 2 * ((1 - P.r * (1 - P.e)) * (P.dM + P.wh - P.w) ^ 2
      + P.r * (1 - P.e) * (P.wh - P.w) ^ 2)) / (P.a * (4 - P.β ^ 2) ^ 2) := by
  have hQ := (Qpos P).ne'
  have ha := P.ha.ne'
  rw [br_eq, br_eq]
  simp only [stage2Profit, s2q_eq, m0, m1, m2]
  generalize P.r * (1 - P.e) = X
  generalize 4 - P.β ^ 2 = Q at hQ ⊢
  field_simp
  ring

lemma slope_neg (hβ : 0 < P.β) : bestResp P 1 - bestResp P 0 < 0 := by
  rw [slope_eq]
  have hX := Xpos P
  have hX1 := Xlt1 P
  have hQ := Qpos P
  have hd : 0 < P.dM + P.wh - P.w := by have := P.hdM; have := P.hw; linarith
  apply div_neg_of_neg_of_pos _ (mul_pos P.ha (pow_pos hQ 2))
  have : 0 < (1 - P.r * (1 - P.e)) * (P.dM + P.wh - P.w) ^ 2 + P.r * (1 - P.e) * (P.wh - P.w) ^ 2 :=
    add_pos_of_pos_of_nonneg (mul_pos (by linarith) (pow_pos hd 2))
      (mul_nonneg hX.le (sq_nonneg _))
  have := mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hβ) (pow_pos hX 2)) this
  linarith

lemma estar_eq : eStarI P = eHatI P / (1 - (bestResp P 1 - bestResp P 0)) := by
  have hQ := Qpos P
  have ha := P.ha
  have hX := Xpos P
  have hX1 := Xlt1 P
  rw [slope_eq]
  have hD : 0 ≤ (1 - P.r * (1 - P.e)) * (P.dM + P.wh - P.w) ^ 2 + P.r * (1 - P.e) * (P.wh - P.w) ^ 2 :=
    add_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (mul_nonneg hX.le (sq_nonneg _))
  have hden : 0 < P.a * (4 - P.β ^ 2) ^ 2 + 4 * P.β * (P.r * (1 - P.e)) ^ 2 *
      ((1 - P.r * (1 - P.e)) * (P.dM + P.wh - P.w) ^ 2 + P.r * (1 - P.e) * (P.wh - P.w) ^ 2) := by
    have := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) P.hβ0) (sq_nonneg (P.r * (1 - P.e)))) hD
    have := mul_pos ha (pow_pos hQ 2)
    linarith
  simp only [eStarI, eHatI]
  generalize P.r * (1 - P.e) = X at hden hD ⊢
  generalize 4 - P.β ^ 2 = Q at hQ hden ⊢
  have hQ' := hQ.ne'
  have ha' := ha.ne'
  have hden' := hden.ne'
  have hN : 0 ≤ 4 * P.β * X ^ 2 * ((1 - X) * (P.dM + P.wh - P.w) ^ 2 + X * (P.wh - P.w) ^ 2) /
      (P.a * Q ^ 2) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) P.hβ0) (sq_nonneg X)) hD)
      (mul_pos ha (pow_pos hQ 2)).le
  rw [div_eq_div_iff]
  · field_simp
    ring
  · intro h; apply hden'; linear_combination h
  · rw [neg_div, sub_neg_eq_add]; exact ne_of_gt (by linarith)


lemma br_bounds (hβ : 0 < P.β) (hint : eHatI P < 1) (y : ℝ) (hy : y ∈ Icc (0:ℝ) 1) :
    0 < bestResp P y ∧ bestResp P y < 1 := by
  have h1 := br1_pos P
  have hs := slope_neg P hβ
  have h0 := br0_eq P
  rw [br_aff P y]
  obtain ⟨hy0, hy1⟩ := hy
  constructor
  · nlinarith
  · nlinarith

/-- Best-response relation of a buyer with own independent effort `x` facing rival effort `y`. -/
def R (K x y : ℝ) : Prop :=
  (x = 0 ∧ P.a / 2 * bestResp P y ^ 2 ≤ K) ∨ (x = bestResp P y ∧ K < P.a / 2 * bestResp P y ^ 2)

lemma opt_iff (hβ : 0 < P.β) (hint : eHatI P < 1) (K x y : ℝ) (hx : x ∈ Icc (0:ℝ) 1)
    (hy : y ∈ Icc (0:ℝ) 1) :
    ((∀ t ∈ StrategySet, expProfit₁ P K t.1 t.2 y 0 ≤ expProfit₁ P K x 0 y 0) ∧
      ((x, (0:ℝ)) ≠ (0, 0) → expProfit₁ P K 0 0 y 0 < expProfit₁ P K x 0 y 0)) ↔ R P K x y := by
  have hb := br_bounds P hβ hint y hy
  have ha := P.ha
  have g := fun x' => gain P K x' y
  set b := bestResp P y with hbdef
  have hbS : ((b, 0) : ℝ × ℝ) ∈ StrategySet :=
    ⟨⟨hb.1.le, hb.2.le⟩, ⟨le_refl _, zero_le_one⟩, mul_zero _⟩
  have eb := g b
  rw [if_pos hb.1] at eb
  -- generic upper bound on deviations
  have H0 : ∀ t1 ∈ Icc (0:ℝ) 1, expProfit₁ P K t1 0 y 0 ≤
      expProfit₁ P K 0 0 y 0 + max 0 (P.a / 2 * b ^ 2 - K) := by
    intro t1 ht1
    have e := g t1
    have hm1 := le_max_left 0 (P.a / 2 * b ^ 2 - K)
    have hm2 := le_max_right 0 (P.a / 2 * b ^ 2 - K)
    rcases ht1.1.eq_or_lt with h | h
    · subst h; simp at e; linarith
    · rw [if_pos h] at e
      nlinarith [sq_nonneg (t1 - b)]
  have H : ∀ t ∈ StrategySet, expProfit₁ P K t.1 t.2 y 0 ≤
      expProfit₁ P K 0 0 y 0 + max 0 (P.a / 2 * b ^ 2 - K) := by
    rintro ⟨t1, t2⟩ ⟨ht1, ht2, ht12⟩
    simp only at ht1 ht2 ht12 ⊢
    rcases ht2.1.eq_or_lt with h | h
    · subst h; exact H0 t1 ht1
    · have : t1 = 0 := by
        rcases mul_eq_zero.1 ht12 with h' | h'
        · exact h'
        · linarith
      subst this
      have hd := dom P hβ K t2 y 0 h hy ⟨le_refl _, zero_le_one⟩
      have := H0 t2 ⟨h.le, ht2.2⟩
      linarith
  constructor
  · rintro ⟨hopt, hstr⟩
    have h1 := hopt (b, 0) hbS
    simp only at h1
    have ex := g x
    rcases hx.1.eq_or_lt with hx0 | hx0
    · subst hx0
      left; refine ⟨rfl, ?_⟩
      linarith
    · rw [if_pos hx0] at ex
      have hs := hstr (by intro h; simp at h; linarith)
      have hxb : x = b := by
        by_contra hne
        have : 0 < (x - b) ^ 2 := by
          have : x - b ≠ 0 := sub_ne_zero.2 hne
          positivity
        nlinarith [mul_pos ha this]
      subst hxb
      right; exact ⟨rfl, by linarith⟩
  · rintro (⟨hx0, hK⟩ | ⟨hxb, hK⟩)
    · subst hx0
      refine ⟨fun t ht => ?_, fun h => absurd rfl h⟩
      have := H t ht
      rw [max_eq_left (by linarith)] at this
      simpa using this
    · subst hxb
      refine ⟨fun t ht => ?_, fun _ => by linarith⟩
      have := H t ht
      rw [max_eq_right (by linarith)] at this
      linarith

lemma eq_iff (hβ : 0 < P.β) (hint : eHatI P < 1) (K : ℝ) (s₁ s₂ : ℝ × ℝ) :
    IsEquilibrium P K s₁ s₂ ↔ s₁.2 = 0 ∧ s₂.2 = 0 ∧ s₁.1 ∈ Icc (0:ℝ) 1 ∧ s₂.1 ∈ Icc (0:ℝ) 1 ∧
      R P K s₁.1 s₂.1 ∧ R P K s₂.1 s₁.1 := by
  rcases s₁ with ⟨x, x2⟩
  rcases s₂ with ⟨y, y2⟩
  simp only
  constructor
  · rintro ⟨hS1, hS2, ho1, ho2, ht1, ht2⟩
    simp only [expProfit₂] at ho2 ht2
    obtain ⟨hx, hx2, hx12⟩ := hS1
    obtain ⟨hy, hy2, hy12⟩ := hS2
    simp only at hx hx2 hx12 hy hy2 hy12 ho1 ho2 ht1 ht2
    have ex2 : x2 = 0 := by
      by_contra hne
      have hpos : 0 < x2 := lt_of_le_of_ne hx2.1 (Ne.symm hne)
      have : x = 0 := by
        rcases mul_eq_zero.1 hx12 with h' | h'
        · exact h'
        · exact absurd h' hne
      subst this
      have := ho1 (x2, 0) ⟨hx2, ⟨le_refl _, zero_le_one⟩, mul_zero _⟩
      have := dom P hβ K x2 y y2 hpos hy hy2
      simp only at *
      linarith
    have ey2 : y2 = 0 := by
      by_contra hne
      have hpos : 0 < y2 := lt_of_le_of_ne hy2.1 (Ne.symm hne)
      have : y = 0 := by
        rcases mul_eq_zero.1 hy12 with h' | h'
        · exact h'
        · exact absurd h' hne
      subst this
      have := ho2 (y2, 0) ⟨hy2, ⟨le_refl _, zero_le_one⟩, mul_zero _⟩
      have := dom P hβ K y2 x x2 hpos hx hx2
      simp only at *
      linarith
    subst ex2 ey2
    exact ⟨rfl, rfl, hx, hy, (opt_iff P hβ hint K x y hx hy).1 ⟨ho1, ht1⟩,
      (opt_iff P hβ hint K y x hy hx).1 ⟨ho2, ht2⟩⟩
  · rintro ⟨ex2, ey2, hx, hy, r1, r2⟩
    subst ex2 ey2
    obtain ⟨ho1, ht1⟩ := (opt_iff P hβ hint K x y hx hy).2 r1
    obtain ⟨ho2, ht2⟩ := (opt_iff P hβ hint K y x hy hx).2 r2
    refine ⟨⟨hx, ⟨le_refl _, zero_le_one⟩, mul_zero _⟩, ⟨hy, ⟨le_refl _, zero_le_one⟩, mul_zero _⟩,
      ho1, ?_, ht1, ?_⟩
    · simpa only [expProfit₂] using ho2
    · simpa only [expProfit₂] using ht2


lemma classify (hβ : 0 < P.β) (hint : eHatI P < 1) (K x y : ℝ) :
    (x ∈ Icc (0:ℝ) 1 ∧ y ∈ Icc (0:ℝ) 1 ∧ R P K x y ∧ R P K y x) ↔
      (x = 0 ∧ y = 0 ∧ P.a / 2 * eHatI P ^ 2 ≤ K) ∨
      (x = 0 ∧ y = eHatI P ∧ P.a / 2 * bestResp P (eHatI P) ^ 2 ≤ K ∧ K < P.a / 2 * eHatI P ^ 2) ∨
      (x = eHatI P ∧ y = 0 ∧ P.a / 2 * bestResp P (eHatI P) ^ 2 ≤ K ∧ K < P.a / 2 * eHatI P ^ 2) ∨
      (x = eStarI P ∧ y = eStarI P ∧ K < P.a / 2 * eStarI P ^ 2) := by
  have hb0 := br0_eq P
  have hsn := slope_neg P hβ
  have h1p := br1_pos P
  have hbd0 := br_bounds P hβ hint 0 ⟨le_refl _, zero_le_one⟩
  rw [hb0] at hbd0
  have hs1 : 0 < 1 - (bestResp P 1 - bestResp P 0) := by linarith
  have hst := estar_eq P
  rw [hb0] at hsn hs1 hst
  have hs1' := hs1.ne'
  have hS0 : 0 < eStarI P := by rw [hst]; exact div_pos hbd0.1 hs1
  have hS1 : eStarI P < 1 := by
    rw [hst, div_lt_one hs1]; linarith
  have hbS : bestResp P (eStarI P) = eStarI P := by
    rw [br_aff P (eStarI P), hst, hb0]
    field_simp
    ring
  have hE : eHatI P ∈ Icc (0:ℝ) 1 := ⟨hbd0.1.le, hbd0.2.le⟩
  have hSI : eStarI P ∈ Icc (0:ℝ) 1 := ⟨hS0.le, hS1.le⟩
  constructor
  · rintro ⟨hx, hy, r1, r2⟩
    rcases r1 with ⟨hx0, h1⟩ | ⟨hxe, h1⟩ <;> rcases r2 with ⟨hy0, h2⟩ | ⟨hye, h2⟩
    · subst hx0 hy0; rw [hb0] at h1; exact Or.inl ⟨rfl, rfl, h1⟩
    · subst hx0; rw [hb0] at hye h2; subst hye
      exact Or.inr (Or.inl ⟨rfl, rfl, h1, h2⟩)
    · subst hy0; rw [hb0] at hxe h1; subst hxe
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h2, h1⟩))
    · have ex := hxe
      have ey := hye
      rw [br_aff P y, hb0] at ex
      rw [br_aff P x, hb0] at ey
      have hxy : x = y := by
        have h : (x - y) * (1 + (bestResp P 1 - eHatI P)) = 0 := by
          linear_combination ex - ey
        rcases mul_eq_zero.1 h with h | h
        · linarith
        · linarith
      subst hxy
      have hxs : x = eStarI P := by
        rw [hst, eq_div_iff hs1.ne']
        linear_combination ex
      subst hxs
      rw [← hxe] at h1
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h1⟩))
  · rintro (⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h1, h2⟩ | ⟨rfl, rfl, h1, h2⟩ | ⟨rfl, rfl, h⟩)
    · refine ⟨⟨le_refl _, zero_le_one⟩, ⟨le_refl _, zero_le_one⟩, Or.inl ⟨rfl, ?_⟩, Or.inl ⟨rfl, ?_⟩⟩
        <;> rw [hb0] <;> exact h
    · refine ⟨⟨le_refl _, zero_le_one⟩, hE, Or.inl ⟨rfl, h1⟩, Or.inr ⟨hb0.symm, ?_⟩⟩
      rw [hb0]; exact h2
    · refine ⟨hE, ⟨le_refl _, zero_le_one⟩, Or.inr ⟨hb0.symm, ?_⟩, Or.inl ⟨rfl, h1⟩⟩
      rw [hb0]; exact h2
    · refine ⟨hSI, hSI, Or.inr ⟨hbS.symm, ?_⟩, Or.inr ⟨hbS.symm, ?_⟩⟩ <;> rw [hbS] <;> exact h

lemma thresholds (hβ : 0 < P.β) (hint : eHatI P < 1) :
    P.a / 2 * bestResp P (eHatI P) ^ 2 < P.a / 2 * eStarI P ^ 2 ∧
      P.a / 2 * eStarI P ^ 2 < P.a / 2 * eHatI P ^ 2 := by
  have hb0 := br0_eq P
  have hsn := slope_neg P hβ
  have h1p := br1_pos P
  have hbd0 := br_bounds P hβ hint 0 ⟨le_refl _, zero_le_one⟩
  rw [hb0] at hbd0
  have hs1 : 0 < 1 - (bestResp P 1 - bestResp P 0) := by linarith
  have hst := estar_eq P
  have hbE : bestResp P (eHatI P) = eHatI P * (1 + (bestResp P 1 - bestResp P 0)) := by
    rw [br_aff P (eHatI P), hb0]; ring
  have hbEpos : 0 < bestResp P (eHatI P) := by
    rw [hbE]; exact mul_pos hbd0.1 (by linarith)
  have hS0 : 0 < eStarI P := by rw [hst]; exact div_pos hbd0.1 hs1
  have hlt1 : bestResp P (eHatI P) < eStarI P := by
    rw [hbE, hst, lt_div_iff₀ hs1]
    nlinarith [mul_pos hbd0.1 (mul_pos (neg_pos.2 hsn) (neg_pos.2 hsn))]
  have hlt2 : eStarI P < eHatI P := by
    rw [hst, div_lt_iff₀ hs1]
    nlinarith [mul_pos hbd0.1 (neg_pos.2 hsn)]
  have ha := P.ha
  constructor
  · have := pow_lt_pow_left₀ hlt1 hbEpos.le two_ne_zero
    nlinarith
  · have := pow_lt_pow_left₀ hlt2 hS0.le two_ne_zero
    nlinarith


lemma ehat_pos (hβ : 0 < P.β) (hint : eHatI P < 1) : 0 < eHatI P := by
  have := br_bounds P hβ hint 0 ⟨le_refl _, zero_le_one⟩
  rw [br0_eq] at this; exact this.1

lemma estar_pos (hβ : 0 < P.β) (hint : eHatI P < 1) : 0 < eStarI P := by
  have hb0 := br0_eq P
  have hsn := slope_neg P hβ
  have hst := estar_eq P
  rw [hb0] at hsn hst
  rw [hst]
  exact div_pos (ehat_pos P hβ hint) (by linarith)

end SupplierAudit.Competition.P2Sol


namespace SupplierAudit.Competition.P2Sol
open SupplierAudit.Competition Set

lemma single_br (r q : ℝ) (hq : 0 ≤ q) (h : ∀ x : ℝ, 0 ≤ x → (r - x) * x ≤ (r - q) * q) :
    (r ≤ 0 ∧ q = 0) ∨ (0 < r ∧ q = r / 2) := by
  rcases le_or_gt r 0 with hr | hr
  · left; refine ⟨hr, ?_⟩
    have := h 0 (le_refl _)
    nlinarith
  · right; refine ⟨hr, ?_⟩
    have := h (r / 2) (by linarith)
    nlinarith [sq_nonneg (q - r / 2)]

lemma cournot_gen (β A₁ c₁ A₂ c₂ : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hp1 : 0 < 2 * (A₁ - c₁) - β * (A₂ - c₂)) (hp2 : 0 < 2 * (A₂ - c₂) - β * (A₁ - c₁)) :
    (∀ q₁ q₂ : ℝ, IsCournotNash β A₁ c₁ A₂ c₂ q₁ q₂ ↔
      q₁ = (2 * (A₁ - c₁) - β * (A₂ - c₂)) / (4 - β ^ 2) ∧
      q₂ = (2 * (A₂ - c₂) - β * (A₁ - c₁)) / (4 - β ^ 2)) ∧
    cournotPayoff β A₁ c₁ ((2 * (A₁ - c₁) - β * (A₂ - c₂)) / (4 - β ^ 2))
      ((2 * (A₂ - c₂) - β * (A₁ - c₁)) / (4 - β ^ 2)) =
      ((2 * (A₁ - c₁) - β * (A₂ - c₂)) / (4 - β ^ 2)) ^ 2 := by
  have hQ : 0 < 4 - β ^ 2 := by nlinarith
  have hQ' := hQ.ne'
  have hm1 : 0 < A₁ - c₁ := by nlinarith
  have hm2 : 0 < A₂ - c₂ := by nlinarith
  have hpay : ∀ A c q q' : ℝ, cournotPayoff β A c q q' = ((A - c - β * q') - q) * q := by
    intro A c q q'; unfold cournotPayoff; ring
  have hr1 : A₁ - c₁ - β * ((2 * (A₂ - c₂) - β * (A₁ - c₁)) / (4 - β ^ 2)) =
      2 * ((2 * (A₁ - c₁) - β * (A₂ - c₂)) / (4 - β ^ 2)) := by
    field_simp; ring
  have hr2 : A₂ - c₂ - β * ((2 * (A₁ - c₁) - β * (A₂ - c₂)) / (4 - β ^ 2)) =
      2 * ((2 * (A₂ - c₂) - β * (A₁ - c₁)) / (4 - β ^ 2)) := by
    field_simp; ring
  refine ⟨fun q₁ q₂ => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨h1, h2, o1, o2⟩
    simp only [hpay] at o1 o2
    rcases single_br _ _ h1 o1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
      rcases single_br _ _ h2 o2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
    · subst b1 b2; nlinarith
    · subst b1; rw [b2] at a1; nlinarith
    · subst b2; rw [b1] at a2; nlinarith
    · constructor
      · rw [eq_div_iff hQ']; nlinarith
      · rw [eq_div_iff hQ']; nlinarith
  · rintro ⟨rfl, rfl⟩
    refine ⟨(div_pos hp1 hQ).le, (div_pos hp2 hQ).le, fun x _ => ?_, fun x _ => ?_⟩
    · rw [hpay, hpay, hr1]; nlinarith [sq_nonneg (x - (2 * (A₁ - c₁) - β * (A₂ - c₂)) / (4 - β ^ 2))]
    · rw [hpay, hpay, hr2]; nlinarith [sq_nonneg (x - (2 * (A₂ - c₂) - β * (A₁ - c₁)) / (4 - β ^ 2))]
  · rw [hpay, hr1]; ring

variable (P : Params)

lemma Mpos : 0 < P.α - P.dM - 2 * P.wh := by have := P.hpos3; linarith

lemma pp (n m : ℕ) (hn : n ≤ 2) (hm : m ≤ 2) (h1 : n ≤ m + 1) (h2 : m ≤ n + 1) :
    0 < 2 * (intercept P n - unitCost P n) - P.β * (intercept P m - unitCost P m) := by
  have := P.hpos1; have := P.hpos2; have := P.hpos3; have := P.hβ0; have := P.hβ1
  have := P.hw; have := P.hdM
  interval_cases n <;> interval_cases m <;> simp only [m0, m1, m2] <;> nlinarith

end SupplierAudit.Competition.P2Sol

open SupplierAudit.Competition in
theorem solution (P : Params) :
    (∀ q₁ q₂ : ℝ,
      IsCournotNash P.β (intercept P 0) (unitCost P 0) (intercept P 0) (unitCost P 0) q₁ q₂ ↔
        q₁ = (P.α - 2 * P.w) / (2 + P.β) ∧ q₂ = (P.α - 2 * P.w) / (2 + P.β)) ∧
    (∀ q₁ q₂ : ℝ,
      IsCournotNash P.β (intercept P 0) (unitCost P 0) (intercept P 1) (unitCost P 1) q₁ q₂ ↔
        q₁ = P.α / (2 + P.β) + (P.β * P.dM - (4 - P.β) * P.w + P.β * P.wh) / (4 - P.β ^ 2) ∧
        q₂ = P.α / (2 + P.β) - (2 * P.dM + 2 * (1 - P.β) * P.w + 2 * P.wh) / (4 - P.β ^ 2)) ∧
    (∀ q₁ q₂ : ℝ,
      IsCournotNash P.β (intercept P 1) (unitCost P 1) (intercept P 1) (unitCost P 1) q₁ q₂ ↔
        q₁ = (P.α - P.dM - P.w - P.wh) / (2 + P.β) ∧ q₂ = (P.α - P.dM - P.w - P.wh) / (2 + P.β)) ∧
    (∀ q₁ q₂ : ℝ,
      IsCournotNash P.β (intercept P 1) (unitCost P 1) (intercept P 2) (unitCost P 2) q₁ q₂ ↔
        q₁ = (P.α - P.dM) / (2 + P.β) - (2 * P.w + 2 * (1 - P.β) * P.wh) / (4 - P.β ^ 2) ∧
        q₂ = (P.α - P.dM) / (2 + P.β) - ((4 - P.β) * P.wh - P.β * P.w) / (4 - P.β ^ 2)) ∧
    (∀ q₁ q₂ : ℝ,
      IsCournotNash P.β (intercept P 2) (unitCost P 2) (intercept P 2) (unitCost P 2) q₁ q₂ ↔
        q₁ = (P.α - P.dM - 2 * P.wh) / (2 + P.β) ∧ q₂ = (P.α - P.dM - 2 * P.wh) / (2 + P.β)) ∧
    (∀ n₁ n₂ : ℕ, n₁ ≤ 2 → n₂ ≤ 2 → n₁ ≤ n₂ + 1 → n₂ ≤ n₁ + 1 →
      0 < stage2q P n₁ n₂ ∧
      IsCournotNash P.β (intercept P n₁) (unitCost P n₁) (intercept P n₂) (unitCost P n₂)
        (stage2q P n₁ n₂) (stage2q P n₂ n₁) ∧
      cournotPayoff P.β (intercept P n₁) (unitCost P n₁) (stage2q P n₁ n₂) (stage2q P n₂ n₁) =
        stage2Profit P n₁ n₂) := by
  have G := fun n m (hn : n ≤ 2) (hm : m ≤ 2) (h1 : n ≤ m + 1) (h2 : m ≤ n + 1) =>
    P2Sol.cournot_gen P.β (intercept P n) (unitCost P n) (intercept P m) (unitCost P m)
      P.hβ0 P.hβ1 (P2Sol.pp P n m hn hm h1 h2) (P2Sol.pp P m n hm hn h2 h1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← P2Sol.tq00]; exact (G 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  · rw [← P2Sol.tq01, ← P2Sol.tq10]
    exact (G 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  · rw [← P2Sol.tq11]; exact (G 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  · rw [← P2Sol.tq12, ← P2Sol.tq21]
    exact (G 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  · rw [← P2Sol.tq22]; exact (G 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  · intro n₁ n₂ hn hm h1 h2
    obtain ⟨g1, g2⟩ := G n₁ n₂ hn hm h1 h2
    refine ⟨?_, (g1 _ _).2 ⟨rfl, rfl⟩, ?_⟩
    · rw [P2Sol.s2q_eq]; exact div_pos (P2Sol.pp P n₁ n₂ hn hm h1 h2) (P2Sol.Qpos P)
    · rw [stage2Profit]; exact g2
