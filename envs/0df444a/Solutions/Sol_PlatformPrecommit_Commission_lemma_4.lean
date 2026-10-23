-- Prove2me | solution 1 for PlatformPrecommit.Commission.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T11:28:30.286114+00:00
-- url     : https://prove2.me/submissions/6e5ff04e-6940-4a4e-acf8-baebb569c2f1

import Mathlib
import Definitions.Def_PlatformPrecommit_Commission_AlphaStar
import Theorems.Thm_PlatformPrecommit_Commission_lemma_F_2

open PlatformPrecommit.Commission
open Filter Topology

namespace L4Aux

/-! ## Algebra of `alphaStar` -/

def Kp (b g a : ℝ) : ℝ :=
  a ^ 2 * (b ^ 3 + b ^ 2 * g - 2 * b ^ 2 - b * g - 2 * b + 3) +
    a * (b ^ 2 * g + b ^ 2 + b * g ^ 2 - b * g - 2 * b - 2 * g ^ 2 + 2) + g ^ 2 - 1

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

theorem alphaStar_facts (M : Model) (hM : M.Standing) :
    Kp M.β M.γ (alphaStar M) = 0 ∧ 0 < alphaStar M ∧ alphaStar M < 1 := by
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
  have hextra : 0 < 4 * ((1 - b) * (1 - g)) * (1 + g) * (3 + b - b ^ 2 - b * g) := by
    have h1 : 0 < (1 - b) * (1 - g) := mul_pos (by linarith) (by linarith)
    have h2 : 0 < 3 + b - b ^ 2 - b * g := by nlinarith
    have : 0 < 1 + g := by linarith
    positivity
  have hR0 : 0 ≤ R := by rw [hRid]; nlinarith [sq_nonneg N]
  have hdef : alphaStar M = (N + Real.sqrt R) / Q := by
    simp only [alphaStar, hN, hR, hQ, b, g]
  set s := Real.sqrt R with hs_def
  have hs : s ^ 2 = R := Real.sq_sqrt hR0
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have haQ : alphaStar M * Q = N + s := by rw [hdef]; field_simp
  have key : 2 * Q * Kp b g (alphaStar M) = (alphaStar M * Q - N) ^ 2 - R := by
    simp only [Kp]; rw [hQ, hN, hR]; ring
  have : (alphaStar M * Q - N) ^ 2 - R = 0 := by rw [haQ]; rw [← hs]; ring
  rw [this] at key
  have h2Q : 2 * Q ≠ 0 := by positivity
  have hK : Kp b g (alphaStar M) = 0 := (mul_eq_zero.mp key).resolve_left h2Q
  have hpos : 0 < alphaStar M := by
    have hNs : 0 < N + s := by
      have : N ^ 2 < s ^ 2 := by rw [hs, hRid]; linarith
      by_contra hc
      push Not at hc
      have h1 : s ≤ -N := by linarith
      have h2 := mul_self_le_mul_self hs0 h1
      nlinarith
    have : 0 < alphaStar M * Q := by rw [haQ]; exact hNs
    exact pos_of_mul_pos_left this hQpos.le
  refine ⟨hK, hpos, ?_⟩
  obtain ⟨S, hS, e⟩ := sign_transfer b g _ 1 hb0 hb1 hg0 hg1 hpos hK zero_le_one
  have hK1 : 0 < Kp b g 1 := by
    have : Kp b g 1 = (1 - b) * (2 - b - g) * (b + g + 2) := by simp only [Kp]; ring
    rw [this]
    have : 0 < 1 - b := by linarith
    have : 0 < 2 - b - g := by linarith
    have : 0 < b + g + 2 := by linarith
    positivity
  rw [e] at hK1
  have := pos_of_mul_pos_left hK1 hS.le
  linarith

/-! ## Second stage: best response of one platform -/

/-- Profit of a platform with commission `α`, facing demand intercept `A` and supply offset `c`. -/
noncomputable def hfun (α A c q : ℝ) : ℝ :=
  (1 - α) * q * min (max (A - q) 0) (max (α * q - c) 0)

theorem hfun_le (α A c : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hc : 0 ≤ c) (q : ℝ) :
    hfun α A c q ≤ hfun α A c ((A + c) / (1 + α)) := by
  set P := (A + c) / (1 + α) with hP
  have h1α : 0 < 1 + α := by linarith
  have hPdef : P * (1 + α) = A + c := by rw [hP]; field_simp
  have hzz : A - P = α * P - c := by linarith
  have hPA : A ≤ 2 * P := by nlinarith
  unfold hfun
  set m := min (max (A - q) 0) (max (α * q - c) 0) with hm
  have hm0 : 0 ≤ m := le_min (le_max_right _ _) (le_max_right _ _)
  have h1a : 0 < 1 - α := by linarith
  rw [hzz, min_self]
  have hRHS : 0 ≤ (1 - α) * P * max (α * P - c) 0 := by
    have : 0 ≤ P := by rw [hP]; positivity
    positivity
  rcases le_or_gt q 0 with hq | hq
  · have : (1 - α) * q * m ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h1a.le hq) hm0
    linarith
  rcases le_or_gt (α * P - c) 0 with hz | hz
  · -- the platform cannot earn a positive profit
    have : m = 0 := by
      rcases le_or_gt (α * q - c) 0 with h | h
      · apply le_antisymm _ hm0
        calc m ≤ max (α * q - c) 0 := min_le_right _ _
          _ = 0 := max_eq_right h
      · have : A - q ≤ 0 := by nlinarith
        apply le_antisymm _ hm0
        calc m ≤ max (A - q) 0 := min_le_left _ _
          _ = 0 := max_eq_right this
    rw [this]; simp only [mul_zero]; exact hRHS
  rw [max_eq_left hz.le]
  rcases le_or_gt q P with hqP | hqP
  · have : m ≤ α * P - c := by
      calc m ≤ max (α * q - c) 0 := min_le_right _ _
        _ ≤ α * P - c := max_le (by nlinarith) hz.le
    have h2 : (1 - α) * q * m ≤ (1 - α) * q * (α * P - c) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    have h3 : (1 - α) * q * (α * P - c) ≤ (1 - α) * P * (α * P - c) := by
      apply mul_le_mul_of_nonneg_right _ hz.le
      exact mul_le_mul_of_nonneg_left hqP h1a.le
    linarith
  · rcases le_or_gt (A - q) 0 with hAq | hAq
    · have : m = 0 := by
        apply le_antisymm _ hm0
        calc m ≤ max (A - q) 0 := min_le_left _ _
          _ = 0 := max_eq_right hAq
      rw [this]; simp only [mul_zero]; positivity
    · have : m ≤ A - q := by
        calc m ≤ max (A - q) 0 := min_le_left _ _
          _ = A - q := max_eq_left hAq.le
      have h2 : (1 - α) * q * m ≤ (1 - α) * q * (A - q) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      have h3 : q * (A - q) ≤ P * (A - P) := by nlinarith
      rw [← hzz]
      nlinarith

/-! ## Second stage: the market-clearing equilibrium -/

noncomputable def det2 (M : Model) (y : Fin 2 → ℝ) : ℝ :=
  (1 + y 0) * (1 + y 1) - (M.γ + M.β * y 0) * (M.γ + M.β * y 1)

/-- The market-clearing equilibrium prices of the second stage. -/
noncomputable def sig (M : Model) (y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => M.Ω * (1 + y (rival i) + M.γ + M.β * y (rival i)) / det2 M y

theorem rival_ne (i : Fin 2) : rival i ≠ i := by
  fin_cases i <;> simp [rival]

theorem rival_rival (i : Fin 2) : rival (rival i) = i := by
  fin_cases i <;> simp [rival]

theorem det2_pos (M : Model) (hM : M.Standing) (y : Fin 2 → ℝ) (hy : AdmissibleAlpha y) :
    0 < det2 M y := by
  obtain ⟨hΩ, hb0, hb1, hg0, hg1⟩ := hM
  obtain ⟨h00, h01⟩ := hy 0
  obtain ⟨h10, h11⟩ := hy 1
  unfold det2
  have u0 : 0 < 1 + y 0 - (M.γ + M.β * y 0) := by nlinarith
  have u1 : 0 < 1 + y 1 - (M.γ + M.β * y 1) := by nlinarith
  have x1 : 0 ≤ M.γ + M.β * y 1 := by nlinarith
  have : (1 + y 0) * (1 + y 1) - (M.γ + M.β * y 0) * (M.γ + M.β * y 1) =
      (1 + y 0) * (1 + y 1 - (M.γ + M.β * y 1)) +
        (M.γ + M.β * y 1) * (1 + y 0 - (M.γ + M.β * y 0)) := by ring
  rw [this]
  have : 0 < 1 + y 0 := by linarith
  positivity

theorem sig_pos (M : Model) (hM : M.Standing) (y : Fin 2 → ℝ) (hy : AdmissibleAlpha y)
    (i : Fin 2) : 0 < sig M y i := by
  have hd := det2_pos M hM y hy
  obtain ⟨hΩ, hb0, hb1, hg0, hg1⟩ := hM
  obtain ⟨h0, h1⟩ := hy (rival i)
  unfold sig
  have : 0 < 1 + y (rival i) + M.γ + M.β * y (rival i) := by nlinarith
  positivity

theorem sig_lin (M : Model) (hM : M.Standing) (y : Fin 2 → ℝ) (hy : AdmissibleAlpha y)
    (i : Fin 2) :
    (1 + y i) * sig M y i = M.Ω + (M.γ + M.β * y (rival i)) * sig M y (rival i) := by
  have hd := (det2_pos M hM y hy).ne'
  fin_cases i <;> simp only [sig, rival] <;> simp at hd ⊢ <;> field_simp <;> simp only [det2] <;> ring

theorem sig_unique (M : Model) (hM : M.Standing) (y : Fin 2 → ℝ) (hy : AdmissibleAlpha y)
    (p : Fin 2 → ℝ)
    (hp : ∀ i, (1 + y i) * p i = M.Ω + (M.γ + M.β * y (rival i)) * p (rival i)) :
    p = sig M y := by
  have hd := det2_pos M hM y hy
  have e0 := hp 0
  have e1 := hp 1
  simp only [rival] at e0 e1
  simp at e0 e1
  have h0 : det2 M y * p 0 = M.Ω * (1 + y 1 + M.γ + M.β * y 1) := by
    simp only [det2]; linear_combination (1 + y 1) * e0 + (M.γ + M.β * y 1) * e1
  have h1 : det2 M y * p 1 = M.Ω * (1 + y 0 + M.γ + M.β * y 0) := by
    simp only [det2]; linear_combination (1 + y 0) * e1 + (M.γ + M.β * y 0) * e0
  funext i
  fin_cases i
  · simp only [sig, rival]; simp; field_simp; linarith
  · simp only [sig, rival]; simp; field_simp; linarith

theorem profC_eq (M : Model) (y p : Fin 2 → ℝ) (i : Fin 2) :
    profC M y p i = hfun (y i) (M.Ω + M.γ * p (rival i)) (M.β * (y (rival i) * p (rival i)))
      (p i) := by
  simp only [profC, matchC, demand, supply, wageC, hfun]
  congr 3; ring

theorem profC_upd (M : Model) (y p : Fin 2 → ℝ) (i : Fin 2) (q : ℝ) :
    profC M y (Function.update p i q) i =
      hfun (y i) (M.Ω + M.γ * p (rival i)) (M.β * (y (rival i) * p (rival i))) q := by
  rw [profC_eq]
  simp only [Function.update_self, Function.update_of_ne (rival_ne i)]

theorem sig_NE (M : Model) (hM : M.Standing) (y : Fin 2 → ℝ) (hy : AdmissibleAlpha y) :
    IsCSubNE M y (sig M y) := by
  refine ⟨trivial, fun i q _ => ?_⟩
  show profC M y (Function.update (sig M y) i q) i ≤ profC M y (sig M y) i
  rw [profC_upd, profC_eq]
  have hlin := sig_lin M hM y hy i
  have hpos := sig_pos M hM y hy (rival i)
  obtain ⟨hΩ, hb0, hb1, hg0, hg1⟩ := hM
  obtain ⟨hy0, hy1⟩ := hy i
  obtain ⟨hr0, hr1⟩ := hy (rival i)
  have hsi : sig M y i = ((M.Ω + M.γ * sig M y (rival i)) +
      M.β * (y (rival i) * sig M y (rival i))) / (1 + y i) := by
    field_simp; linarith
  rw [hsi]
  apply hfun_le _ _ _ hy0 hy1 (by positivity) (by positivity)

/-- Profit at the market-clearing equilibrium. -/
theorem prof_sig (M : Model) (hM : M.Standing) (y : Fin 2 → ℝ) (hy : AdmissibleAlpha y)
    (j : Fin 2) :
    profC M y (sig M y) j = (1 - y j) * sig M y j *
      max (y j * sig M y j - M.β * (y (rival j) * sig M y (rival j))) 0 := by
  have hlin := sig_lin M hM y hy j
  simp only [profC, matchC, demand, supply, wageC]
  have : M.Ω - sig M y j + M.γ * sig M y (rival j) =
      y j * sig M y j - M.β * (y (rival j) * sig M y (rival j)) := by linarith
  rw [this, min_self]

theorem posNE_eq (M : Model) (hM : M.Standing) (y : Fin 2 → ℝ) (hy : AdmissibleAlpha y)
    (p : Fin 2 → ℝ) (hp : IsCSubNE M y p) (hpos : ∀ i, 0 < profC M y p i) : p = sig M y := by
  have hF := lemma_F_2 M hM y p hy hp hpos
  apply sig_unique M hM y hy p
  intro i
  have hdi := hF i
  have hpi := hpos i
  simp only [profC, matchC] at hpi
  rw [hdi, min_self] at hpi
  have hs : 0 < supply M (wageC y p) i := by
    by_contra h
    push Not at h
    have h0 : supply M (wageC y p) i = 0 := le_antisymm h (le_max_right _ _)
    rw [h0, mul_zero] at hpi
    exact lt_irrefl _ hpi
  have hd : 0 < demand M p i := by rw [hdi]; exact hs
  simp only [supply, wageC] at hs hdi
  simp only [demand] at hd hdi
  have hs' := hs
  have hd' := hd
  rw [lt_max_iff] at hs' hd'
  simp only [lt_irrefl, or_false] at hs' hd'
  rw [max_eq_left hs'.le, max_eq_left hd'.le] at hdi
  linarith

theorem sig_sel (M : Model) (hM : M.Standing) (y : Fin 2 → ℝ) (hy : AdmissibleAlpha y) :
    IsSelCSubNE M y (sig M y) := by
  refine ⟨sig_NE M hM y hy, ?_⟩
  rintro ⟨p', hp', hpos'⟩
  rw [← posNE_eq M hM y hy p' hp' hpos']
  exact hpos'

/-! ## First stage: a unilateral deviation from a symmetric profile -/

def Dd (b g a v : ℝ) : ℝ := (1 + v) * (1 + a) - (g + b * v) * (g + b * a)
def f1 (b g a v : ℝ) : ℝ := v * (1 + g + a * (1 - b ^ 2)) - b * a * (1 + g)
def f2 (b g a v : ℝ) : ℝ := a * (1 + g) + v * (a * (1 - b ^ 2) - b * (1 + g))
def cc (b g a : ℝ) : ℝ := 1 + a + g + b * a
def Qf (b g a v : ℝ) : ℝ := (1 - v) * f1 b g a v
noncomputable def Gd (Ω b g a v : ℝ) : ℝ :=
  (1 - v) * (Ω * cc b g a / Dd b g a v) * max (Ω * f1 b g a v / Dd b g a v) 0

theorem Dd_pos (b g a v : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : 0 < Dd b g a v := by
  unfold Dd
  have u0 : 0 < 1 + v - (g + b * v) := by nlinarith
  have u1 : 0 < 1 + a - (g + b * a) := by nlinarith
  have x1 : 0 ≤ g + b * a := by positivity
  have : (1 + v) * (1 + a) - (g + b * v) * (g + b * a) =
      (1 + v) * (1 + a - (g + b * a)) + (g + b * a) * (1 + v - (g + b * v)) := by ring
  rw [this]
  have : 0 < 1 + v := by linarith
  positivity

theorem f1_self_pos (b g a : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (ha0 : 0 < a) : 0 < f1 b g a a := by
  have : f1 b g a a = a * ((1 - b) * (1 + g) + a * ((1 - b) * (1 + b))) := by
    unfold f1; ring
  rw [this]
  have : 0 < 1 - b := by linarith
  have : 0 < 1 + g := by linarith
  have : 0 < 1 + b := by linarith
  positivity

theorem f2_self_pos (b g a : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (ha0 : 0 < a) : 0 < f2 b g a a := by
  have : f2 b g a a = a * ((1 - b) * (1 + g) + a * ((1 - b) * (1 + b))) := by
    unfold f2; ring
  rw [this]
  have : 0 < 1 - b := by linarith
  have : 0 < 1 + g := by linarith
  have : 0 < 1 + b := by linarith
  positivity

theorem key_identity (b g a v : ℝ) :
    Qf b g a v * Dd b g a a ^ 2 - Qf b g a a * Dd b g a v ^ 2 =
      (v - a) * (-(Dd b g a a * cc b g a * Kp b g a) +
        (v - a) * (-((1 + g + a * (1 - b ^ 2)) * Dd b g a a ^ 2 +
          Qf b g a a * (1 + a - b * g - b ^ 2 * a) ^ 2))) := by
  unfold Qf Dd cc Kp f1; ring

theorem Gd_pos_eq (Ω b g a v : ℝ) (hΩ : 0 < Ω) (hD : 0 < Dd b g a v) (hf : 0 ≤ f1 b g a v) :
    Gd Ω b g a v = Ω ^ 2 * cc b g a * Qf b g a v / Dd b g a v ^ 2 := by
  unfold Gd Qf
  rw [max_eq_left (div_nonneg (mul_nonneg hΩ.le hf) hD.le)]
  field_simp

theorem Gd_nonpos_eq (Ω b g a v : ℝ) (hΩ : 0 < Ω) (hD : 0 < Dd b g a v) (hf : f1 b g a v ≤ 0) :
    Gd Ω b g a v = 0 := by
  unfold Gd
  rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hΩ.le hf) hD.le)]
  ring

theorem cc_pos (b g a : ℝ) (hb0 : 0 ≤ b) (hg0 : 0 ≤ g) (ha0 : 0 ≤ a) : 0 < cc b g a := by
  unfold cc; positivity

/-- At a root of `Kp`, the symmetric commission is a global best reply. -/
theorem dev_le (Ω b g a v : ℝ) (hΩ : 0 < Ω) (hb0 : 0 ≤ b) (hb1 : b < 1) (hg0 : 0 ≤ g)
    (hg1 : g < 1) (ha0 : 0 < a) (ha1 : a < 1) (hK : Kp b g a = 0) (hv0 : 0 < v) (hv1 : v < 1) :
    Gd Ω b g a v ≤ Gd Ω b g a a := by
  have hDa := Dd_pos b g a a hb0 hb1 hg0 hg1 ha0.le ha1.le ha0.le ha1.le
  have hDv := Dd_pos b g a v hb0 hb1 hg0 hg1 ha0.le ha1.le hv0.le hv1.le
  have hfa := f1_self_pos b g a hb0 hb1 hg0 hg1 ha0
  have hc := cc_pos b g a hb0 hg0 ha0.le
  have hQa : 0 ≤ Qf b g a a := by unfold Qf; exact mul_nonneg (by linarith) hfa.le
  rw [Gd_pos_eq Ω b g a a hΩ hDa hfa.le]
  rcases le_or_gt (f1 b g a v) 0 with hf | hf
  · rw [Gd_nonpos_eq Ω b g a v hΩ hDv hf]; positivity
  rw [Gd_pos_eq Ω b g a v hΩ hDv hf.le, div_le_div_iff₀ (by positivity) (by positivity)]
  have hid := key_identity b g a v
  rw [hK] at hid
  have hW1 : 0 ≤ (1 + g + a * (1 - b ^ 2)) * Dd b g a a ^ 2 +
      Qf b g a a * (1 + a - b * g - b ^ 2 * a) ^ 2 := by
    have : 0 ≤ 1 + g + a * (1 - b ^ 2) := by nlinarith
    positivity
  have hle : Qf b g a v * Dd b g a a ^ 2 ≤ Qf b g a a * Dd b g a v ^ 2 := by
    have : (v - a) * (-(Dd b g a a * cc b g a * 0) + (v - a) * -((1 + g + a * (1 - b ^ 2)) *
        Dd b g a a ^ 2 + Qf b g a a * (1 + a - b * g - b ^ 2 * a) ^ 2)) ≤ 0 := by
      have : (v - a) * (-(Dd b g a a * cc b g a * 0) + (v - a) * -((1 + g + a * (1 - b ^ 2)) *
          Dd b g a a ^ 2 + Qf b g a a * (1 + a - b * g - b ^ 2 * a) ^ 2)) =
          -((v - a) ^ 2 * ((1 + g + a * (1 - b ^ 2)) * Dd b g a a ^ 2 +
            Qf b g a a * (1 + a - b * g - b ^ 2 * a) ^ 2)) := by ring
      rw [this]; apply neg_nonpos.mpr; positivity
    linarith
  have hk : 0 ≤ Ω ^ 2 * cc b g a := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hle hk]

/-- Away from a root of `Kp`, some nearby deviation is strictly profitable while keeping both
platforms' market-clearing quantities positive. -/
theorem dev_gt (Ω b g a : ℝ) (hΩ : 0 < Ω) (hb0 : 0 ≤ b) (hb1 : b < 1) (hg0 : 0 ≤ g)
    (hg1 : g < 1) (ha0 : 0 < a) (ha1 : a < 1) (hK : Kp b g a ≠ 0) :
    ∃ v, 0 < v ∧ v < 1 ∧ 0 < f1 b g a v ∧ 0 < f2 b g a v ∧ Gd Ω b g a a < Gd Ω b g a v := by
  have hDa := Dd_pos b g a a hb0 hb1 hg0 hg1 ha0.le ha1.le ha0.le ha1.le
  have hfa := f1_self_pos b g a hb0 hb1 hg0 hg1 ha0
  have hf2a := f2_self_pos b g a hb0 hb1 hg0 hg1 ha0
  have hc := cc_pos b g a hb0 hg0 ha0.le
  set W0 := -(Dd b g a a * cc b g a * Kp b g a) with hW0
  set W1 := -((1 + g + a * (1 - b ^ 2)) * Dd b g a a ^ 2 +
          Qf b g a a * (1 + a - b * g - b ^ 2 * a) ^ 2) with hW1
  have hW0ne : W0 ≠ 0 := by
    rw [hW0]; apply neg_ne_zero.mpr
    exact mul_ne_zero (mul_ne_zero hDa.ne' hc.ne') hK
  -- open conditions near `a`
  have e1 : ∀ᶠ v in 𝓝 a, 0 < f1 b g a v := by
    have hcont : Continuous fun v => f1 b g a v := by unfold f1; fun_prop
    exact (hcont.tendsto a).eventually (lt_mem_nhds hfa)
  have e2 : ∀ᶠ v in 𝓝 a, 0 < f2 b g a v := by
    have hcont : Continuous fun v => f2 b g a v := by unfold f2; fun_prop
    exact (hcont.tendsto a).eventually (lt_mem_nhds hf2a)
  have e3 : ∀ᶠ v in 𝓝 a, 0 < W0 * (W0 + (v - a) * W1) := by
    have hcont : Continuous fun v => W0 * (W0 + (v - a) * W1) := by fun_prop
    have : 0 < W0 * (W0 + (a - a) * W1) := by
      simp only [sub_self, zero_mul, add_zero]
      exact mul_self_pos.mpr hW0ne
    exact (hcont.tendsto a).eventually (lt_mem_nhds this)
  have e4 : ∀ᶠ v in 𝓝 a, 0 < v := lt_mem_nhds ha0
  have e5 : ∀ᶠ v in 𝓝 a, v < 1 := gt_mem_nhds ha1
  have e := e1.and (e2.and (e3.and (e4.and e5)))
  have hside : ∃ v, (0 < f1 b g a v ∧ 0 < f2 b g a v ∧ 0 < W0 * (W0 + (v - a) * W1) ∧
      0 < v ∧ v < 1) ∧ 0 < W0 * (v - a) := by
    rcases lt_or_gt_of_ne hW0ne with hneg | hpos
    · obtain ⟨v, hv, hlt⟩ := ((e.filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin : Set.Iio a ∈ 𝓝[Set.Iio a] a)).exists
      exact ⟨v, hv, by have : v < a := hlt; nlinarith⟩
    · obtain ⟨v, hv, hlt⟩ := ((e.filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin : Set.Ioi a ∈ 𝓝[Set.Ioi a] a)).exists
      exact ⟨v, hv, by have : a < v := hlt; nlinarith⟩
  obtain ⟨v, ⟨hf1, hf2, h3, hv0, hv1⟩, hs⟩ := hside
  refine ⟨v, hv0, hv1, hf1, hf2, ?_⟩
  have hDv := Dd_pos b g a v hb0 hb1 hg0 hg1 ha0.le ha1.le hv0.le hv1.le
  rw [Gd_pos_eq Ω b g a a hΩ hDa hfa.le, Gd_pos_eq Ω b g a v hΩ hDv hf1.le,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  have hid := key_identity b g a v
  have hprod : 0 < (v - a) * (W0 + (v - a) * W1) := by
    have h := mul_pos hs h3
    have : W0 * (v - a) * (W0 * (W0 + (v - a) * W1)) =
        W0 ^ 2 * ((v - a) * (W0 + (v - a) * W1)) := by ring
    rw [this] at h
    exact pos_of_mul_pos_right h (sq_nonneg _)
  have hlt : Qf b g a a * Dd b g a v ^ 2 < Qf b g a v * Dd b g a a ^ 2 := by
    have : Qf b g a v * Dd b g a a ^ 2 - Qf b g a a * Dd b g a v ^ 2 =
        (v - a) * (W0 + (v - a) * W1) := by rw [hid]
    linarith
  have hk : 0 < Ω ^ 2 * cc b g a := by positivity
  nlinarith [mul_lt_mul_of_pos_left hlt hk]

/-! ## Profits after a unilateral deviation -/

theorem upd_adm (a v : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hv0 : 0 < v) (hv1 : v < 1) (i : Fin 2) :
    AdmissibleAlpha (Function.update (fun _ : Fin 2 => a) i v) := by
  intro j
  by_cases h : j = i
  · subst h; simp only [Function.update_self]; exact ⟨hv0, hv1⟩
  · rw [Function.update_of_ne h]; exact ⟨ha0, ha1⟩

theorem fin_cases_rival (i j : Fin 2) : j = i ∨ j = rival i := by
  fin_cases i <;> fin_cases j <;> simp [rival]

theorem devProf (M : Model) (hM : M.Standing) (a v : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hv0 : 0 < v) (hv1 : v < 1) (i : Fin 2) :
    profC M (Function.update (fun _ : Fin 2 => a) i v)
        (sig M (Function.update (fun _ : Fin 2 => a) i v)) i = Gd M.Ω M.β M.γ a v ∧
    (0 < f1 M.β M.γ a v → 0 < f2 M.β M.γ a v → ∀ j,
      0 < profC M (Function.update (fun _ : Fin 2 => a) i v)
        (sig M (Function.update (fun _ : Fin 2 => a) i v)) j) := by
  set y := Function.update (fun _ : Fin 2 => a) i v with hy_def
  have hy : AdmissibleAlpha y := upd_adm a v ha0 ha1 hv0 hv1 i
  have hyi : y i = v := by rw [hy_def]; exact Function.update_self _ _ _
  have hyr : y (rival i) = a := by rw [hy_def, Function.update_of_ne (rival_ne i)]
  obtain ⟨hΩ, hb0, hb1, hg0, hg1⟩ := hM
  have hdet : det2 M y = Dd M.β M.γ a v := by
    rw [hy_def]; fin_cases i <;> simp [det2, Dd, Function.update] <;> ring
  have hD := Dd_pos M.β M.γ a v hb0 hb1 hg0 hg1 ha0.le ha1.le hv0.le hv1.le
  have hsi : sig M y i = M.Ω * cc M.β M.γ a / Dd M.β M.γ a v := by
    simp only [sig, hyr, hdet, cc]
  have hsr : sig M y (rival i) = M.Ω * (1 + v + M.γ + M.β * v) / Dd M.β M.γ a v := by
    simp only [sig, rival_rival, hyi, hdet]
  have hM' : M.Standing := ⟨hΩ, hb0, hb1, hg0, hg1⟩
  have pi := prof_sig M hM' y hy i
  have pr := prof_sig M hM' y hy (rival i)
  rw [rival_rival] at pr
  have zi : y i * sig M y i - M.β * (y (rival i) * sig M y (rival i)) =
      M.Ω * f1 M.β M.γ a v / Dd M.β M.γ a v := by
    rw [hyi, hyr, hsi, hsr]; field_simp; simp only [cc, f1]; ring
  have zr : y (rival i) * sig M y (rival i) - M.β * (y i * sig M y i) =
      M.Ω * f2 M.β M.γ a v / Dd M.β M.γ a v := by
    rw [hyi, hyr, hsi, hsr]; field_simp; simp only [cc, f2]; ring
  refine ⟨?_, ?_⟩
  · rw [pi, zi, hyi, hsi]; rfl
  · intro h1 h2 j
    have hci := cc_pos M.β M.γ a hb0 hg0 ha0.le
    rcases fin_cases_rival i j with rfl | rfl
    · rw [pi, zi, hyi, hsi, max_eq_left (by positivity)]
      have : 0 < 1 - v := by linarith
      positivity
    · rw [pr, zr, hyr, hsr, max_eq_left (by positivity)]
      have : 0 < 1 - a := by linarith
      have : 0 < 1 + v + M.γ + M.β * v := by positivity
      positivity

theorem upd_self (a : ℝ) (i : Fin 2) :
    Function.update (fun _ : Fin 2 => a) i a = fun _ => a := by
  funext j; by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

end L4Aux

open L4Aux in
theorem solution (M : Model) (hM : M.Standing) :
    (∃ σ : (Fin 2 → ℝ) → (Fin 2 → ℝ),
      IsCSPE M (fun _ => alphaStar M) σ) ∧
    (∀ α σ, IsCSPE M α σ → Symmetric α → ∀ i,
      α i = alphaStar M ∧
      (σ α) i = M.Ω / (1 - M.γ + (1 - M.β) * alphaStar M) ∧
      profC M α (σ α) i =
        alphaStar M * (1 - M.β) * (1 - alphaStar M) /
          (1 + alphaStar M - M.γ - M.β * alphaStar M) ^ 2 * M.Ω ^ 2) := by
  obtain ⟨hKs, has0, has1⟩ := alphaStar_facts M hM
  have hM' := hM
  obtain ⟨hΩ, hb0, hb1, hg0, hg1⟩ := hM'
  refine ⟨⟨sig M, fun y hy => sig_sel M hM y hy, fun _ => ⟨has0, has1⟩, ?_⟩, ?_⟩
  · intro i v hv0 hv1
    rw [(devProf M hM _ v has0 has1 hv0 hv1 i).1]
    have h := (devProf M hM _ _ has0 has1 has0 has1 i).1
    rw [upd_self] at h
    rw [h]
    exact dev_le _ _ _ _ v hΩ hb0 hb1 hg0 hg1 has0 has1 hKs hv0 hv1
  · intro α σ hσ hsym
    obtain ⟨hsel, hadm, hdev⟩ := hσ
    obtain ⟨a, rfl⟩ : ∃ a : ℝ, α = fun _ => a := by
      refine ⟨α 0, ?_⟩
      funext j; fin_cases j
      · rfl
      · exact hsym.symm
    obtain ⟨ha0, ha1⟩ := hadm 0
    -- in subgames where both platforms can profit, `σ` plays the market-clearing prices
    have hσeq : ∀ i v, 0 < v → v < 1 → 0 < f1 M.β M.γ a v → 0 < f2 M.β M.γ a v →
        σ (Function.update (fun _ : Fin 2 => a) i v) =
          sig M (Function.update (fun _ : Fin 2 => a) i v) := by
      intro i v hv0 hv1 h1 h2
      have hy := upd_adm a v ha0 ha1 hv0 hv1 i
      obtain ⟨hne, hselc⟩ := hsel _ hy
      have hpos := hselc ⟨_, sig_NE M hM _ hy, (devProf M hM a v ha0 ha1 hv0 hv1 i).2 h1 h2⟩
      exact posNE_eq M hM _ hy _ hne hpos
    have hσa : σ (fun _ => a) = sig M (fun _ => a) := by
      have := hσeq 0 a ha0 ha1 (f1_self_pos _ _ _ hb0 hb1 hg0 hg1 ha0)
        (f2_self_pos _ _ _ hb0 hb1 hg0 hg1 ha0)
      rwa [upd_self] at this
    have hKa : Kp M.β M.γ a = 0 := by
      by_contra hK
      obtain ⟨v, hv0, hv1, h1, h2, hlt⟩ := dev_gt M.Ω M.β M.γ a hΩ hb0 hb1 hg0 hg1 ha0 ha1 hK
      have hd := hdev 0 v hv0 hv1
      rw [hσeq 0 v hv0 hv1 h1 h2, (devProf M hM a v ha0 ha1 hv0 hv1 0).1, hσa] at hd
      have h := (devProf M hM a a ha0 ha1 ha0 ha1 0).1
      rw [upd_self] at h
      rw [h] at hd
      linarith
    have haa : a = alphaStar M := by
      obtain ⟨S, hS, e⟩ := sign_transfer M.β M.γ (alphaStar M) a hb0 hb1 hg0 hg1 has0 hKs ha0.le
      rw [hKa] at e
      have := (mul_eq_zero.mp e.symm).resolve_right hS.ne'
      linarith
    subst haa
    intro i
    have hE : 0 < 1 + alphaStar M - M.γ - M.β * alphaStar M := by nlinarith
    have hC : 0 < 1 + alphaStar M + M.γ + M.β * alphaStar M := by nlinarith
    have hsigv : ∀ j, sig M (fun _ => alphaStar M) j =
        M.Ω / (1 - M.γ + (1 - M.β) * alphaStar M) := by
      intro j
      simp only [sig, det2]
      have : (1 + alphaStar M) * (1 + alphaStar M) -
          (M.γ + M.β * alphaStar M) * (M.γ + M.β * alphaStar M) =
          (1 + alphaStar M - M.γ - M.β * alphaStar M) *
            (1 + alphaStar M + M.γ + M.β * alphaStar M) := by ring
      rw [this]
      have : 1 - M.γ + (1 - M.β) * alphaStar M = 1 + alphaStar M - M.γ - M.β * alphaStar M := by
        ring
      rw [this]
      field_simp
    refine ⟨rfl, by rw [hσa]; exact hsigv i, ?_⟩
    rw [hσa, prof_sig M hM _ (fun _ => ⟨has0, has1⟩) i]
    simp only [hsigv]
    have : 1 - M.γ + (1 - M.β) * alphaStar M = 1 + alphaStar M - M.γ - M.β * alphaStar M := by
      ring
    rw [this]
    have hz : 0 ≤ alphaStar M * (M.Ω / (1 + alphaStar M - M.γ - M.β * alphaStar M)) -
        M.β * (alphaStar M * (M.Ω / (1 + alphaStar M - M.γ - M.β * alphaStar M))) := by
      have : 0 ≤ alphaStar M * (M.Ω / (1 + alphaStar M - M.γ - M.β * alphaStar M)) := by
        positivity
      nlinarith
    rw [max_eq_left hz]
    field_simp
