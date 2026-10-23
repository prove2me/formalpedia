-- Prove2me | solution 1 for PlatformPrecommit.Commission.proposition_3b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T11:09:57.735516+00:00
-- url     : https://prove2.me/submissions/1989791e-dd87-472d-b0c3-2c4fe81aa380

import Theorems.Thm_PlatformPrecommit_Commission_lemma_1
import Theorems.Thm_PlatformPrecommit_Commission_lemma_4

open PlatformPrecommit.Commission

namespace P3bAux

/-- The quadratic whose positive root is `alphaStar`. -/
def Kp (b g a : ℝ) : ℝ :=
  a ^ 2 * (b ^ 3 + b ^ 2 * g - 2 * b ^ 2 - b * g - 2 * b + 3) +
    a * (b ^ 2 * g + b ^ 2 + b * g ^ 2 - b * g - 2 * b - 2 * g ^ 2 + 2) + g ^ 2 - 1

def Hp (b g : ℝ) : ℝ :=
  4*b^4*g^3 - 14*b^4*g^2 + 12*b^4*g - 2*b^4 + 4*b^3*g^4 - 20*b^3*g^3 + 34*b^3*g^2
    - 11*b^3*g - 5*b^3 - 14*b^2*g^4 + 36*b^2*g^3 - 11*b^2*g^2 - 39*b^2*g + 22*b^2
    + 14*b*g^4 - 21*b*g^3 - 27*b*g^2 + 56*b*g - 16*b - 3*g^4 - g^3 + 18*g^2 - 16*g

def Mq (b g : ℝ) : ℝ := b ^ 2 - 2 * b * g ^ 2 + 6 * b * g - 6 * b + 3 * g ^ 2 - 8 * g + 6

theorem Hp_nonpos (b g : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    Hp b g ≤ 0 := by
  have hu : 0 ≤ 1 - b := by linarith
  have hv : 0 ≤ 1 - g := by linarith
  set u := 1 - b with hu_def
  set v := 1 - g with hv_def
  have e : Hp b g = -((2:ℝ)*u^0*b^4*v^3*g^1 + (1:ℝ)*u^0*b^4*v^4*g^0 + (6:ℝ)*u^1*b^3*v^2*g^2 + (21:ℝ)*u^1*b^3*v^3*g^1 + (9:ℝ)*u^1*b^3*v^4*g^0 + (6:ℝ)*u^2*b^2*v^1*g^3 + (41:ℝ)*u^2*b^2*v^2*g^2 + (71:ℝ)*u^2*b^2*v^3*g^1 + (26:ℝ)*u^2*b^2*v^4*g^0 + (2:ℝ)*u^3*b^1*v^0*g^4 + (23:ℝ)*u^3*b^1*v^1*g^3 + (75:ℝ)*u^3*b^1*v^2*g^2 + (72:ℝ)*u^3*b^1*v^3*g^1 + (16:ℝ)*u^3*b^1*v^4*g^0 + (2:ℝ)*u^4*b^0*v^0*g^4 + (13:ℝ)*u^4*b^0*v^1*g^3 + (30:ℝ)*u^4*b^0*v^2*g^2 + (16:ℝ)*u^4*b^0*v^3*g^1) := by
    simp only [hu_def, hv_def, Hp]; ring
  rw [e]
  apply neg_nonpos.mpr
  positivity

/-- Sign transfer: for `t ≥ 0`, `Kp t` has the sign of `t - a`. -/
theorem sign_transfer (b g a t : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (ha : 0 < a) (hK : Kp b g a = 0) (ht : 0 ≤ t) :
    ∃ S, 0 < S ∧ Kp b g t = (t - a) * S := by
  set P2 := b ^ 3 + b ^ 2 * g - 2 * b ^ 2 - b * g - 2 * b + 3 with hP2
  set P1 := b ^ 2 * g + b ^ 2 + b * g ^ 2 - b * g - 2 * b - 2 * g ^ 2 + 2 with hP1
  have hP2pos : 0 < P2 := by
    have : P2 = (1 - b) * (3 + b * (1 - g) - b ^ 2) := by rw [hP2]; ring
    rw [this]
    apply mul_pos (by linarith)
    nlinarith [mul_nonneg hb0 (by linarith : (0:ℝ) ≤ 1 - g)]
  have hKa : a * (P2 * a + P1) = 1 - g ^ 2 := by
    simp only [Kp] at hK; rw [hP2, hP1]; linarith
  have hlin : 0 < P2 * a + P1 := by
    have : 0 < a * (P2 * a + P1) := by rw [hKa]; nlinarith
    exact pos_of_mul_pos_right this ha.le
  refine ⟨P2 * t + (P2 * a + P1), by nlinarith, ?_⟩
  have : Kp b g t = Kp b g t - Kp b g a := by rw [hK]; ring
  rw [this]; simp only [Kp]; rw [hP2, hP1]; ring

theorem le_of_Kp_nonneg (b g a t : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (ha : 0 < a) (hK : Kp b g a = 0) (ht : 0 ≤ t) (hKt : 0 ≤ Kp b g t) : a ≤ t := by
  obtain ⟨S, hS, e⟩ := sign_transfer b g a t hb0 hb1 hg0 hg1 ha hK ht
  rw [e] at hKt
  by_contra h
  push Not at h
  nlinarith

theorem ge_of_Kp_nonpos (b g a t : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (ha : 0 < a) (hK : Kp b g a = 0) (ht : 0 ≤ t) (hKt : Kp b g t ≤ 0) : t ≤ a := by
  obtain ⟨S, hS, e⟩ := sign_transfer b g a t hb0 hb1 hg0 hg1 ha hK ht
  rw [e] at hKt
  by_contra h
  push Not at h
  nlinarith

/-- `a * Mq ≥ 2(1-b)(1-g)^2` for the positive root `a`. -/
theorem L_nonneg (b g a : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (ha : 0 < a) (hK : Kp b g a = 0) :
    2 * (1 - b) * (1 - g) ^ 2 ≤ a * Mq b g := by
  have hM : 0 < Mq b g := by
    have : Mq b g = (1 - b) ^ 2 + 2 * (1 - b) * (1 - g) ^ 2 + 2 * (1 - b) * (1 - g)
        + (1 - g) ^ 2 := by simp only [Mq]; ring
    rw [this]
    have : 0 < 1 - b := by linarith
    have : 0 < 1 - g := by linarith
    positivity
  set t := 2 * (1 - b) * (1 - g) ^ 2 / Mq b g with ht_def
  have htM : t * Mq b g = 2 * (1 - b) * (1 - g) ^ 2 := by
    rw [ht_def]; field_simp
  have ht0 : 0 ≤ t := by
    rw [ht_def]; apply div_nonneg _ hM.le
    have : 0 ≤ 1 - b := by linarith
    positivity
  have hKt : Mq b g ^ 2 * Kp b g t = (g - 1) * (b + g - 2) * Hp b g := by
    have e : Mq b g ^ 2 * Kp b g t =
        (b ^ 3 + b ^ 2 * g - 2 * b ^ 2 - b * g - 2 * b + 3) * (t * Mq b g) ^ 2 +
        (b ^ 2 * g + b ^ 2 + b * g ^ 2 - b * g - 2 * b - 2 * g ^ 2 + 2) * (t * Mq b g) * Mq b g
        + (g ^ 2 - 1) * Mq b g ^ 2 := by simp only [Kp]; ring
    rw [e, htM]; simp only [Mq, Hp]; ring
  have hH := Hp_nonpos b g hb0 hb1.le hg0 hg1.le
  have hKt' : Kp b g t ≤ 0 := by
    have h1 : 0 < (g - 1) * (b + g - 2) := by nlinarith
    have h2 : Mq b g ^ 2 * Kp b g t ≤ 0 := by rw [hKt]; nlinarith
    have h3 : 0 < Mq b g ^ 2 := by positivity
    nlinarith
  have := ge_of_Kp_nonpos b g a t hb0 hb1 hg0 hg1 ha hK ht0 hKt'
  calc 2 * (1 - b) * (1 - g) ^ 2 = t * Mq b g := htM.symm
    _ ≤ a * Mq b g := mul_le_mul_of_nonneg_right this hM.le

theorem r_sign_le (b g a : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (ha : 0 < a) (hK : Kp b g a = 0) (h : 0 ≤ (b - g) * (2 * b * g + b - 3 * g)) :
    (3 - 2 * b) * a ≤ 1 := by
  have h3 : 0 < 3 - 2 * b := by linarith
  have e : (3 - 2 * b) ^ 2 * Kp b g (1 / (3 - 2 * b)) =
      (1 - b) * ((b - g) * (2 * b * g + b - 3 * g)) := by
    simp only [Kp]; field_simp; ring
  have hKt : 0 ≤ Kp b g (1 / (3 - 2 * b)) := by
    have : 0 ≤ (3 - 2 * b) ^ 2 * Kp b g (1 / (3 - 2 * b)) := by
      rw [e]; exact mul_nonneg (by linarith) h
    have h2 : 0 < (3 - 2 * b) ^ 2 := by positivity
    exact nonneg_of_mul_nonneg_right (by linarith [this, mul_comm ((3 - 2 * b) ^ 2) (Kp b g (1 / (3 - 2 * b)))]) h2
  have := le_of_Kp_nonneg b g a _ hb0 hb1 hg0 hg1 ha hK (by positivity) hKt
  rw [le_div_iff₀ h3] at this; linarith

theorem r_sign_ge (b g a : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (ha : 0 < a) (hK : Kp b g a = 0) (h : (b - g) * (2 * b * g + b - 3 * g) ≤ 0) :
    1 ≤ (3 - 2 * b) * a := by
  have h3 : 0 < 3 - 2 * b := by linarith
  have e : (3 - 2 * b) ^ 2 * Kp b g (1 / (3 - 2 * b)) =
      (1 - b) * ((b - g) * (2 * b * g + b - 3 * g)) := by
    simp only [Kp]; field_simp; ring
  have hKt : Kp b g (1 / (3 - 2 * b)) ≤ 0 := by
    have h1 : (3 - 2 * b) ^ 2 * Kp b g (1 / (3 - 2 * b)) ≤ 0 := by
      rw [e]; exact mul_nonpos_of_nonneg_of_nonpos (by linarith) h
    have h2 : 0 < (3 - 2 * b) ^ 2 := by positivity
    nlinarith
  have := ge_of_Kp_nonpos b g a _ hb0 hb1 hg0 hg1 ha hK (by positivity) hKt
  rw [div_le_iff₀ h3] at this; linarith


theorem Kp_alphaStar (M : Model) (hM : M.Standing) : Kp M.β M.γ (alphaStar M) = 0 := by
  obtain ⟨hΩ, hb0, hb1, hg0, hg1⟩ := hM
  set b := M.β
  set g := M.γ
  set N := b * (3 - g ^ 2) - b ^ 2 * (g + 1) - (1 - g) * (2 + 2 * g + b) with hN
  set R := (1 + g) * (b ^ 4 * (1 + g) - 2 * b ^ 3 * g * (3 - g) +
       b ^ 2 * g * (12 - 11 * g + g ^ 2) - 4 * b * (1 - g) * (4 + 2 * g - g ^ 2) +
       4 * (4 - 4 * g - g ^ 2 + g ^ 3)) with hR
  set Q := 2 * (1 - b) * (3 + (1 - g) * b - b ^ 2) with hQ
  have hQpos : 0 < Q := by
    rw [hQ]
    have : 0 < 3 + (1 - g) * b - b ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - g) hb0]
    have : 0 < 1 - b := by linarith
    positivity
  have hRid : R = N ^ 2 + 4 * ((1 - b) * (1 - g)) * (1 + g) * (3 + b - b ^ 2 - b * g) := by
    rw [hR, hN]; ring
  have hR0 : 0 ≤ R := by
    rw [hRid]
    have h1 : 0 ≤ (1 - b) * (1 - g) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ 3 + b - b ^ 2 - b * g := by nlinarith
    have : 0 ≤ 4 * ((1 - b) * (1 - g)) * (1 + g) * (3 + b - b ^ 2 - b * g) := by
      have : 0 ≤ 1 + g := by linarith
      positivity
    nlinarith [sq_nonneg N]
  have hdef : alphaStar M = (N + Real.sqrt R) / Q := by
    simp only [alphaStar, hN, hR, hQ, b, g]
  set s := Real.sqrt R with hs_def
  have hs : s ^ 2 = R := Real.sq_sqrt hR0
  have haQ : alphaStar M * Q = N + s := by rw [hdef]; field_simp
  have key : 2 * Q * Kp b g (alphaStar M) = (alphaStar M * Q - N) ^ 2 - R := by
    simp only [Kp]; rw [hQ, hN, hR]; ring
  have : (alphaStar M * Q - N) ^ 2 - R = 0 := by rw [haQ]; rw [← hs]; ring
  rw [this] at key
  have h2Q : 2 * Q ≠ 0 := by positivity
  exact (mul_eq_zero.mp key).resolve_left h2Q

theorem cmp_core (b g Ω a : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (hΩ : 0 < Ω) (ha0 : 0 < a) (ha1 : a < 1)
    (hL : 2 * (1 - b) * (1 - g) ^ 2 ≤ a * Mq b g) :
    let D := 4 - 3 * b - 3 * g + 2 * b * g
    let E := 1 - g + (1 - b) * a
    let r := 1 - (3 - 2 * b) * a
    0 < D ∧ 0 < E ∧
    (3 - 2 * b) / D * Ω - Ω / E = -(Ω * (1 - b) * r) / (D * E) ∧
    a * (Ω / E) - 1 / D * Ω = -(Ω * (1 - g) * r) / (D * E) ∧
    (1 - b) * a * Ω / E - (1 - b) / D * Ω = -(Ω * (1 - b) * (1 - g) * r) / (D * E) ∧
    a * (1 - b) * (1 - a) / (1 + a - g - b * a) ^ 2 * Ω ^ 2 - 2 * (1 - b) ^ 2 / D ^ 2 * Ω ^ 2
      = Ω ^ 2 * (1 - b) * r * (a * Mq b g - 2 * (1 - b) * (1 - g) ^ 2) / (D ^ 2 * E ^ 2) := by
  intro D E r
  have hD : 0 < D := by
    show 0 < 4 - 3 * b - 3 * g + 2 * b * g
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - b) (by linarith : (0:ℝ) ≤ 1 - g)]
  have hE : 0 < E := by
    show 0 < 1 - g + (1 - b) * a
    nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - b) ha0]
  have hE' : 1 + a - g - b * a = E := by show _ = 1 - g + (1 - b) * a; ring
  refine ⟨hD, hE, ?_, ?_, ?_, ?_⟩
  · field_simp; simp only [D, E, r]; ring
  · field_simp; simp only [D, E, r]; ring
  · field_simp; simp only [D, E, r]; ring
  · rw [hE']; field_simp; simp only [D, E, r, Mq]; ring

theorem matchC_val (M : Model) (α σ : Fin 2 → ℝ) (a p : ℝ) (ha : ∀ j, α j = a) (hp : ∀ j, σ j = p)
    (z : ℝ) (hz : 0 ≤ z) (h1 : M.Ω - p + M.γ * p = z) (h2 : a * p - M.β * (a * p) = z) (i : Fin 2) :
    matchC M α σ i = z := by
  simp only [matchC, demand, supply, wageC, hp, ha]
  rw [h1, h2, max_eq_left hz, min_self]

theorem CPrefP_of (M : Model) (hM : M.Standing) (hr : (3 - 2 * M.β) * alphaStar M ≤ 1) :
    CPrefP M := by
  intro α σ hσ hsym pw hpw hpos i
  have hM' := hM
  obtain ⟨hΩ, hb0, hb1, hg0, hg1⟩ := hM'
  have l1 := lemma_1 M hM
  dsimp only at l1
  have l4 := (lemma_4 M hM).2 α σ hσ hsym
  have hadm : 0 < alphaStar M ∧ alphaStar M < 1 := by
    have := hσ.2.1 0; rw [(l4 0).1] at this; exact this
  set a := alphaStar M with ha_def
  have hK := Kp_alphaStar M hM
  rw [← ha_def] at hK
  have hL := L_nonneg M.β M.γ a hb0 hb1 hg0 hg1 hadm.1 hK
  obtain ⟨hD, hE, c1, c2, c3, c4⟩ := cmp_core M.β M.γ M.Ω a hb0 hb1 hg0 hg1 hΩ hadm.1 hadm.2 hL
  obtain ⟨e1, e2, e3, e4⟩ := l1.2 pw hpw hpos i
  obtain ⟨_, ep, eprof⟩ := l4 i
  have hmC : matchC M α (σ α) i = (1 - M.β) * a * M.Ω / (1 - M.γ + (1 - M.β) * a) := by
    apply matchC_val M α (σ α) a (M.Ω / (1 - M.γ + (1 - M.β) * a)) (fun j => (l4 j).1)
      (fun j => (l4 j).2.1)
    · exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) hadm.1.le) hΩ.le) hE.le
    · field_simp <;> ring
    · field_simp <;> ring
  have hw : wageC α (σ α) i = a * (M.Ω / (1 - M.γ + (1 - M.β) * a)) := by
    simp only [wageC, ep, (l4 i).1]
  have hr0 : 0 ≤ 1 - (3 - 2 * M.β) * a := by linarith
  have hDE : 0 < (4 - 3 * M.β - 3 * M.γ + 2 * M.β * M.γ) * (1 - M.γ + (1 - M.β) * a) :=
    mul_pos hD hE
  have hb' : 0 ≤ 1 - M.β := by linarith
  have hg' : 0 ≤ 1 - M.γ := by linarith
  have hLn : 0 ≤ a * Mq M.β M.γ - 2 * (1 - M.β) * (1 - M.γ) ^ 2 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1, ep]
    have : -(M.Ω * (1 - M.β) * (1 - (3 - 2 * M.β) * a)) /
        ((4 - 3 * M.β - 3 * M.γ + 2 * M.β * M.γ) * (1 - M.γ + (1 - M.β) * a)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by have := mul_nonneg (mul_nonneg hΩ.le hb') hr0; linarith)
        hDE.le
    linarith
  · rw [e4, eprof]
    have : 0 ≤ M.Ω ^ 2 * (1 - M.β) * (1 - (3 - 2 * M.β) * a) *
        (a * Mq M.β M.γ - 2 * (1 - M.β) * (1 - M.γ) ^ 2) /
        ((4 - 3 * M.β - 3 * M.γ + 2 * M.β * M.γ) ^ 2 * (1 - M.γ + (1 - M.β) * a) ^ 2) := by
      positivity
    linarith
  · rw [hw, e2]
    have : -(M.Ω * (1 - M.γ) * (1 - (3 - 2 * M.β) * a)) /
        ((4 - 3 * M.β - 3 * M.γ + 2 * M.β * M.γ) * (1 - M.γ + (1 - M.β) * a)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by have := mul_nonneg (mul_nonneg hΩ.le hg') hr0; linarith)
        hDE.le
    linarith
  · rw [hmC, e3]
    have : -(M.Ω * (1 - M.β) * (1 - M.γ) * (1 - (3 - 2 * M.β) * a)) /
        ((4 - 3 * M.β - 3 * M.γ + 2 * M.β * M.γ) * (1 - M.γ + (1 - M.β) * a)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (by have := mul_nonneg (mul_nonneg (mul_nonneg hΩ.le hb') hg') hr0; linarith) hDE.le
    linarith

theorem PPrefC_of (M : Model) (hM : M.Standing) (hr : 1 ≤ (3 - 2 * M.β) * alphaStar M) :
    PPrefC M := by
  intro α σ hσ hsym pw hpw hpos i
  have hM' := hM
  obtain ⟨hΩ, hb0, hb1, hg0, hg1⟩ := hM'
  have l1 := lemma_1 M hM
  dsimp only at l1
  have l4 := (lemma_4 M hM).2 α σ hσ hsym
  have hadm : 0 < alphaStar M ∧ alphaStar M < 1 := by
    have := hσ.2.1 0; rw [(l4 0).1] at this; exact this
  set a := alphaStar M with ha_def
  have hK := Kp_alphaStar M hM
  rw [← ha_def] at hK
  have hL := L_nonneg M.β M.γ a hb0 hb1 hg0 hg1 hadm.1 hK
  obtain ⟨hD, hE, c1, c2, c3, c4⟩ := cmp_core M.β M.γ M.Ω a hb0 hb1 hg0 hg1 hΩ hadm.1 hadm.2 hL
  obtain ⟨e1, e2, e3, e4⟩ := l1.2 pw hpw hpos i
  obtain ⟨_, ep, eprof⟩ := l4 i
  have hmC : matchC M α (σ α) i = (1 - M.β) * a * M.Ω / (1 - M.γ + (1 - M.β) * a) := by
    apply matchC_val M α (σ α) a (M.Ω / (1 - M.γ + (1 - M.β) * a)) (fun j => (l4 j).1)
      (fun j => (l4 j).2.1)
    · exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) hadm.1.le) hΩ.le) hE.le
    · field_simp <;> ring
    · field_simp <;> ring
  have hw : wageC α (σ α) i = a * (M.Ω / (1 - M.γ + (1 - M.β) * a)) := by
    simp only [wageC, ep, (l4 i).1]
  have hr0 : 0 ≤ (3 - 2 * M.β) * a - 1 := by linarith
  have hDE : 0 < (4 - 3 * M.β - 3 * M.γ + 2 * M.β * M.γ) * (1 - M.γ + (1 - M.β) * a) :=
    mul_pos hD hE
  have hb' : 0 ≤ 1 - M.β := by linarith
  have hg' : 0 ≤ 1 - M.γ := by linarith
  have hLn : 0 ≤ a * Mq M.β M.γ - 2 * (1 - M.β) * (1 - M.γ) ^ 2 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1, ep]
    have : 0 ≤ -(M.Ω * (1 - M.β) * (1 - (3 - 2 * M.β) * a)) /
        ((4 - 3 * M.β - 3 * M.γ + 2 * M.β * M.γ) * (1 - M.γ + (1 - M.β) * a)) :=
      div_nonneg (by have := mul_nonneg (mul_nonneg hΩ.le hb') hr0; linarith) hDE.le
    linarith
  · rw [e4, eprof]
    have : 0 ≤ M.Ω ^ 2 * (1 - M.β) * ((3 - 2 * M.β) * a - 1) *
        (a * Mq M.β M.γ - 2 * (1 - M.β) * (1 - M.γ) ^ 2) /
        ((4 - 3 * M.β - 3 * M.γ + 2 * M.β * M.γ) ^ 2 * (1 - M.γ + (1 - M.β) * a) ^ 2) := by
      positivity
    have e : M.Ω ^ 2 * (1 - M.β) * (1 - (3 - 2 * M.β) * a) *
        (a * Mq M.β M.γ - 2 * (1 - M.β) * (1 - M.γ) ^ 2) /
        ((4 - 3 * M.β - 3 * M.γ + 2 * M.β * M.γ) ^ 2 * (1 - M.γ + (1 - M.β) * a) ^ 2) =
        -(M.Ω ^ 2 * (1 - M.β) * ((3 - 2 * M.β) * a - 1) *
        (a * Mq M.β M.γ - 2 * (1 - M.β) * (1 - M.γ) ^ 2) /
        ((4 - 3 * M.β - 3 * M.γ + 2 * M.β * M.γ) ^ 2 * (1 - M.γ + (1 - M.β) * a) ^ 2)) := by
      ring
    linarith
  · rw [hw, e2]
    have : 0 ≤ -(M.Ω * (1 - M.γ) * (1 - (3 - 2 * M.β) * a)) /
        ((4 - 3 * M.β - 3 * M.γ + 2 * M.β * M.γ) * (1 - M.γ + (1 - M.β) * a)) :=
      div_nonneg (by have := mul_nonneg (mul_nonneg hΩ.le hg') hr0; linarith) hDE.le
    linarith
  · rw [hmC, e3]
    have : 0 ≤ -(M.Ω * (1 - M.β) * (1 - M.γ) * (1 - (3 - 2 * M.β) * a)) /
        ((4 - 3 * M.β - 3 * M.γ + 2 * M.β * M.γ) * (1 - M.γ + (1 - M.β) * a)) :=
      div_nonneg (by have := mul_nonneg (mul_nonneg (mul_nonneg hΩ.le hb') hg') hr0; linarith)
        hDE.le
    linarith

end P3bAux

open P3bAux in
theorem solution (Ω : ℝ) (hΩ : 0 < Ω) :
    (∀ β γ, (⟨Ω, β, γ⟩ : Model).Standing →
      (∃ α σ, IsCSPE ⟨Ω, β, γ⟩ α σ ∧ Symmetric α) ∧
      (∃ pw, IsPNE ⟨Ω, β, γ⟩ pw ∧ ∀ i, 0 < profP ⟨Ω, β, γ⟩ pw i)) ∧
    (∀ β γ, (⟨Ω, β, γ⟩ : Model).Standing → β ≤ γ →
      CPrefP ⟨Ω, β, γ⟩) ∧
    (∀ β, 0 < β → β < 1 → ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ β ∧
      ∀ γ, 0 ≤ γ → γ < γ₀ → CPrefP ⟨Ω, β, γ⟩) ∧
    (∀ β, 0 ≤ β → β < 1 → ∃ δ : ℝ, 0 < δ ∧
      ∀ γ, 0 ≤ γ → γ ≤ β → β - δ < γ → PPrefC ⟨Ω, β, γ⟩) := by
  -- the sign of `(3 - 2β) α* - 1` is controlled by `(β - γ)(2βγ + β - 3γ)`
  have hC : ∀ β γ, (⟨Ω, β, γ⟩ : Model).Standing →
      0 ≤ (β - γ) * (2 * β * γ + β - 3 * γ) → CPrefP ⟨Ω, β, γ⟩ := by
    intro β γ hM h
    apply CPrefP_of _ hM
    have hK := Kp_alphaStar _ hM
    obtain ⟨σ, hσ⟩ := (lemma_4 _ hM).1
    have hadm := hσ.2.1 0
    obtain ⟨_, hb0, hb1, hg0, hg1⟩ := hM
    exact r_sign_le β γ _ hb0 hb1 hg0 hg1 hadm.1 hK h
  have hP : ∀ β γ, (⟨Ω, β, γ⟩ : Model).Standing →
      (β - γ) * (2 * β * γ + β - 3 * γ) ≤ 0 → PPrefC ⟨Ω, β, γ⟩ := by
    intro β γ hM h
    apply PPrefC_of _ hM
    have hK := Kp_alphaStar _ hM
    obtain ⟨σ, hσ⟩ := (lemma_4 _ hM).1
    have hadm := hσ.2.1 0
    obtain ⟨_, hb0, hb1, hg0, hg1⟩ := hM
    exact r_sign_ge β γ _ hb0 hb1 hg0 hg1 hadm.1 hK h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro β γ hM
    refine ⟨?_, ?_⟩
    · obtain ⟨σ, hσ⟩ := (lemma_4 _ hM).1
      exact ⟨_, σ, hσ, rfl⟩
    · have l1 := lemma_1 _ hM
      dsimp only at l1
      exact ⟨_, l1.1⟩
  · intro β γ hM hbg
    apply hC β γ hM
    obtain ⟨_, hb0, hb1, hg0, hg1⟩ := hM
    have h1 : β - γ ≤ 0 := by linarith
    have h2 : 2 * β * γ + β - 3 * γ ≤ 0 := by nlinarith
    exact mul_nonneg_of_nonpos_of_nonpos h1 h2
  · intro β hb0 hb1
    have h3 : 0 < 3 - 2 * β := by linarith
    refine ⟨β / (3 - 2 * β), by positivity, ?_, ?_⟩
    · rw [div_le_iff₀ h3]; nlinarith
    · intro γ hg0 hg
      rw [lt_div_iff₀ h3] at hg
      have hgb : γ < β := by nlinarith
      apply hC β γ ⟨hΩ, hb0.le, hb1, hg0, by linarith⟩
      apply mul_nonneg (by linarith) (by linarith)
  · intro β hb0 hb1
    rcases hb0.eq_or_lt with h | h
    · refine ⟨1, one_pos, ?_⟩
      intro γ hg0 hgb _
      apply hP β γ ⟨hΩ, hb0, hb1, hg0, by linarith⟩
      have : γ = β := by linarith
      rw [this]; simp
    · have h3 : 0 < 3 - 2 * β := by linarith
      refine ⟨β - β / (3 - 2 * β), ?_, ?_⟩
      · have : β / (3 - 2 * β) < β := by rw [div_lt_iff₀ h3]; nlinarith
        linarith
      · intro γ hg0 hgb hlt
        have hg' : β / (3 - 2 * β) < γ := by linarith
        rw [div_lt_iff₀ h3] at hg'
        apply hP β γ ⟨hΩ, hb0, hb1, hg0, by linarith⟩
        apply mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
