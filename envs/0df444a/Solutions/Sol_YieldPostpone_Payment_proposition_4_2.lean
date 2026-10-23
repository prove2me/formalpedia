-- Prove2me | solution 2 for YieldPostpone.Payment.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T05:04:16.271321+00:00
-- url     : https://prove2.me/submissions/97596f11-6152-41b9-8885-b0fc76baf0fd

import Theorems.Thm_YieldPostpone_Payment_lemma_1_corrected
import Theorems.Thm_YieldPostpone_Payment_lemma_2
import Theorems.Thm_YieldPostpone_Payment_lemma_3
import Theorems.Thm_YieldPostpone_Payment_lemma_4
import Theorems.Thm_YieldPostpone_Payment_oa_threshold_order
import Theorems.Thm_YieldPostpone_Payment_responsive_threshold_order

open YieldPostpone.Payment

/-- Square comparison: `0 ≤ x < y` gives `x^2 < y^2`. -/
private lemma sq_lt_sq_of (x y : ℝ) (hx : 0 ≤ x) (h : x < y) : x ^ 2 < y ^ 2 := by
  nlinarith

/-- Basic facts on the valid parameters, with `s = √μ`. -/
private lemma base_facts (P : Params) (hP : P.Valid) :
    0 < P.μ ∧ P.α < P.μ ∧ P.μ < 1 ∧ P.μ = P.α * (1 - P.θ) + P.θ := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have h1θ : 0 < 1 - P.θ := by linarith
  have h1α : 0 < 1 - P.α := by linarith
  refine ⟨?_, ?_, ?_, hμ⟩
  · rw [hμ]; positivity
  · rw [hμ]; nlinarith [mul_pos hθ0 h1α]
  · rw [hμ]; nlinarith [mul_pos h1θ h1α]

/-- `cDA = a α s (1-s) / (b (s-α))` with `s = √μ`, in multiplied-out form. -/
private lemma cDA_eq (P : Params) (hP : P.Valid) :
    cDA P * (P.b * (Real.sqrt P.μ - P.α)) =
      P.a * P.α * Real.sqrt P.μ * (1 - Real.sqrt P.μ) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 ≤ P.μ := by
    rw [hμ]
    have : 0 < 1 - P.θ := by linarith
    positivity
  have hs : Real.sqrt P.μ ^ 2 = P.μ := Real.sq_sqrt hμ0
  unfold cDA
  set s := Real.sqrt P.μ
  have hαθ : P.b * (P.α + P.θ) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, div_eq_iff hαθ]
  rw [hμ] at hs ⊢
  linear_combination (P.a * P.α * P.b * P.α) * hs

/-- The OA-to-DA facts used in Proposition 4(A). -/
private lemma A_facts (P : Params) (hP : P.Valid) :
    ∃ s t : ℝ, 0 < s ∧ s ^ 2 = P.μ ∧ 0 < t ∧
      t ^ 2 = P.α * (2 - P.α) * (1 - P.θ) + P.θ ∧ P.α * t < P.μ ∧
      Cbar P * (P.b * (P.μ - P.α * t)) = P.a * P.α * P.μ * (1 - t) ∧
      cDA P * (P.b * (s - P.α)) = P.a * P.α * s * (1 - s) ∧ 0 < s - P.α ∧
      0 < Cbar P ∧ Cbar P < cDA P ∧ cDA P < P.a * P.α / P.b := by
  obtain ⟨hμpos, hαμ, hμ1, hμ⟩ := base_facts P hP
  have hcDA := cDA_eq P hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have h1θ : 0 < 1 - P.θ := by linarith
  have h1α : 0 < 1 - P.α := by linarith
  -- s = √μ, t = √phiC
  have hs2 : Real.sqrt P.μ ^ 2 = P.μ := Real.sq_sqrt hμpos.le
  have hphiC : phiC P = P.α * (1 - P.θ) * (2 - P.α) + P.θ := rfl
  have hphiCpos : 0 < phiC P := by
    rw [hphiC]
    have : 0 < 2 - P.α := by linarith
    positivity
  have ht2 : Real.sqrt (phiC P) ^ 2 = phiC P := Real.sq_sqrt hphiCpos.le
  have hμphiC : P.μ < phiC P := by
    rw [hphiC, hμ]; nlinarith [mul_pos (mul_pos hα0 h1θ) h1α]
  have hphiC1 : phiC P < 1 := by
    rw [hphiC]; nlinarith [mul_pos h1θ (mul_pos h1α h1α)]
  have hst : Real.sqrt P.μ < Real.sqrt (phiC P) := Real.sqrt_lt_sqrt hμpos.le hμphiC
  have ht1 : Real.sqrt (phiC P) < 1 := by
    rw [Real.sqrt_lt' (by norm_num)]; linarith
  have hspos : 0 < Real.sqrt P.μ := Real.sqrt_pos.mpr hμpos
  have htpos : 0 < Real.sqrt (phiC P) := Real.sqrt_pos.mpr hphiCpos
  -- Cbar closed form
  have hphiB : phiB P * (1 - P.α) = P.μ ^ 2 - P.α ^ 2 * phiC P := by
    unfold phiB phiA; rw [hphiC, hμ]; ring
  have hphiBpos : 0 < phiB P := by
    have : 0 < P.μ ^ 2 - P.α ^ 2 * phiC P := by
      have : P.α ^ 2 * phiC P < P.α ^ 2 := by
        have := mul_lt_mul_of_pos_left hphiC1 (pow_pos hα0 2); linarith
      nlinarith
    rw [← hphiB] at this
    by_contra hcon
    push Not at hcon
    have := mul_nonpos_of_nonpos_of_nonneg hcon h1α.le
    linarith
  set s := Real.sqrt P.μ with hsdef
  set t := Real.sqrt (phiC P) with htdef
  clear_value s t
  have hCbar : Cbar P * (P.b * (P.μ - P.α * t)) = P.a * P.α * P.μ * (1 - t) := by
    have hdef : Cbar P = (P.a * P.α / P.b) * ((phiA P - P.θ * P.μ * t) / phiB P) := by
      rw [htdef]; rfl
    rw [hdef]
    have hid : (phiA P - P.θ * P.μ * t) * (P.μ - P.α * t) = P.μ * (1 - t) * phiB P := by
      unfold phiB phiA
      rw [← ht2] at hphiC
      rw [hμ]
      linear_combination (P.α * P.θ * (P.α * (1 - P.θ) + P.θ)) * hphiC
    have hb0 : P.b ≠ 0 := hb.ne'
    have hB0 : phiB P ≠ 0 := hphiBpos.ne'
    rw [show P.a * P.α / P.b * ((phiA P - P.θ * P.μ * t) / phiB P) * (P.b * (P.μ - P.α * t)) =
        P.a * P.α * ((phiA P - P.θ * P.μ * t) * (P.μ - P.α * t)) / phiB P by
          field_simp]
    rw [hid]
    field_simp
  have hαt : P.α * t < P.μ := by
    have : P.α * t < P.α := by nlinarith
    linarith
  have hsα : 0 < s - P.α := by nlinarith
  have hμαt : 0 < P.μ - P.α * t := by linarith
  have hCbar' : Cbar P = P.a * P.α * P.μ * (1 - t) / (P.b * (P.μ - P.α * t)) :=
    eq_div_of_mul_eq (by positivity) hCbar
  have hcDA' : cDA P = P.a * P.α * s * (1 - s) / (P.b * (s - P.α)) :=
    eq_div_of_mul_eq (by positivity) hcDA
  have h1t : 0 < 1 - t := by linarith
  have h1s : 0 < 1 - s := by nlinarith
  have hcDAlt : cDA P < P.a * P.α / P.b := by
    rw [hcDA', div_lt_div_iff₀ (by positivity) hb]
    have h3 : 0 < (s - P.α) - s * (1 - s) := by nlinarith
    have e : P.a * P.α * (P.b * (s - P.α)) - P.a * P.α * s * (1 - s) * P.b =
        P.a * P.α * P.b * ((s - P.α) - s * (1 - s)) := by ring
    have : 0 < P.a * P.α * P.b * ((s - P.α) - s * (1 - s)) := by positivity
    linarith
  have hCD : Cbar P < cDA P := by
    rw [hCbar', hcDA', div_lt_div_iff₀ (by positivity) (by positivity)]
    rw [← hs2]
    have hid : P.a * P.α * s * (1 - s) * (P.b * (s ^ 2 - P.α * t)) -
        P.a * P.α * s ^ 2 * (1 - t) * (P.b * (s - P.α)) =
        P.a * P.α * P.b * s * ((t - s) * (s ^ 2 - P.α)) := by ring
    have : 0 < P.a * P.α * P.b * s * ((t - s) * (s ^ 2 - P.α)) := by
      have : 0 < t - s := by linarith
      have : 0 < s ^ 2 - P.α := by linarith
      positivity
    linarith
  have ht2' : t ^ 2 = P.α * (2 - P.α) * (1 - P.θ) + P.θ := by rw [ht2, hphiC]; ring
  refine ⟨s, t, hspos, hs2, htpos, ht2', hαt, hCbar, hcDA, hsα, ?_, hCD, hcDAlt⟩
  rw [hCbar']; positivity

/-- Cross-multiplication. -/
private lemma fc2 (X Y m n : ℝ) (hm : 0 < m) (hn : 0 < n) (h : n * X < m * Y) :
    X / m < Y / n := by
  rw [div_lt_div_iff₀ hm hn]; linarith

/-- Core OA3-vs-DA1 profit comparison. -/
private lemma coreA (a b α μ s c : ℝ) (hα : 0 < α) (hs : s ^ 2 = μ)
    (hbc : b * c < a * α) (hαμ : a * α ≤ a * μ)
    (h1 : c * (b * (s - α)) < a * α * s * (1 - s)) :
    α ^ 2 * (a * μ - b * c) ^ 2 < μ * (b * c - a * α) ^ 2 := by
  have key : α * (a * μ - b * c) < s * (a * α - b * c) := by
    rw [← hs]; linarith
  have hX : 0 ≤ α * (a * μ - b * c) := by
    have : 0 ≤ a * μ - b * c := by linarith
    positivity
  have := sq_lt_sq_of _ _ hX key
  have e1 : (α * (a * μ - b * c)) ^ 2 = α ^ 2 * (a * μ - b * c) ^ 2 := by ring
  have e2 : (s * (a * α - b * c)) ^ 2 = μ * (b * c - a * α) ^ 2 := by rw [← hs]; ring
  rw [e1, e2] at this; exact this

/-- Core OA3-vs-DA1 consumer-surplus comparison, `c < Cbar`. -/
private lemma coreA_CS1 (a b α μ t c φ : ℝ) (hα : 0 < α) (ht : 0 < t) (ht2 : t ^ 2 = φ)
    (hbc : b * c < a * μ)
    (h1 : c * (b * (μ - α * t)) < a * α * μ * (1 - t)) :
    α ^ 2 * (a * μ - b * c) ^ 2 * φ < μ ^ 2 * (b * c - a * α) ^ 2 := by
  have key : α * t * (a * μ - b * c) < μ * (a * α - b * c) := by linarith
  have hX : 0 ≤ α * t * (a * μ - b * c) := by
    have : 0 ≤ a * μ - b * c := by linarith
    positivity
  have := sq_lt_sq_of _ _ hX key
  have e1 : (α * t * (a * μ - b * c)) ^ 2 = α ^ 2 * (a * μ - b * c) ^ 2 * φ := by
    rw [← ht2]; ring
  have e2 : (μ * (a * α - b * c)) ^ 2 = μ ^ 2 * (b * c - a * α) ^ 2 := by ring
  rw [e1, e2] at this; exact this

/-- Core OA3-vs-DA1 consumer-surplus comparison, `c > Cbar`. -/
private lemma coreA_CS2 (a b α μ t c φ : ℝ) (hμ : 0 < μ) (ht2 : t ^ 2 = φ)
    (hbc : b * c < a * α)
    (h1 : a * α * μ * (1 - t) < c * (b * (μ - α * t))) :
    μ ^ 2 * (b * c - a * α) ^ 2 < α ^ 2 * (a * μ - b * c) ^ 2 * φ := by
  have key : μ * (a * α - b * c) < α * t * (a * μ - b * c) := by linarith
  have hX : 0 ≤ μ * (a * α - b * c) := by
    have : 0 ≤ a * α - b * c := by linarith
    positivity
  have := sq_lt_sq_of _ _ hX key
  have e1 : (α * t * (a * μ - b * c)) ^ 2 = α ^ 2 * (a * μ - b * c) ^ 2 * φ := by
    rw [← ht2]; ring
  have e2 : (μ * (a * α - b * c)) ^ 2 = μ ^ 2 * (b * c - a * α) ^ 2 := by ring
  rw [e1, e2] at this; exact this

private lemma A_cmp (P : Params) (hP : P.Valid) :
    0 < Cbar P ∧ Cbar P < cDA P ∧
    (∀ c, 0 < c → c < cDA P →
      (OA3 P c).1 < (DA1 P c).1 ∧ (OA3 P c).2.1 < (DA1 P c).2.1) ∧
    (∀ c, 0 < c → c < Cbar P → (OA3 P c).2.2 < (DA1 P c).2.2) ∧
    (∀ c, Cbar P < c → c < cDA P → (DA1 P c).2.2 < (OA3 P c).2.2) := by
  obtain ⟨hμpos, hαμ, hμ1, hμ⟩ := base_facts P hP
  obtain ⟨s, t, hs0, hs2, ht0, ht2, hαt, hCbar, hcDA, hsα, hC0, hCD, hDa⟩ := A_facts P hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hαμ' : P.a * P.α ≤ P.a * P.μ := (mul_lt_mul_of_pos_left hαμ ha).le
  have hbc_of : ∀ c, c < P.a * P.α / P.b → P.b * c < P.a * P.α := by
    intro c hc
    rwa [lt_div_iff₀ hb, mul_comm] at hc
  have hμαt : 0 < P.b * (P.μ - P.α * t) := by
    have : 0 < P.μ - P.α * t := by linarith
    positivity
  have hsαb : 0 < P.b * (s - P.α) := by positivity
  refine ⟨hC0, hCD, ?_, ?_, ?_⟩
  · intro c hc0 hc
    have hbc := hbc_of c (lt_trans hc hDa)
    have h1 : c * (P.b * (s - P.α)) < P.a * P.α * s * (1 - s) := by
      rw [← hcDA]; exact mul_lt_mul_of_pos_right hc hsαb
    have core := coreA P.a P.b P.α P.μ s c hα0 hs2 hbc hαμ' h1
    constructor
    · show (P.a * P.μ - P.b * c) ^ 2 / (16 * P.b * P.μ) <
        (P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2)
      apply fc2 _ _ _ _ (by positivity) (by positivity)
      have := mul_lt_mul_of_pos_left core (by positivity : (0:ℝ) < 16 * P.b)
      linarith
    · show (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * P.μ) <
        (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2)
      apply fc2 _ _ _ _ (by positivity) (by positivity)
      have := mul_lt_mul_of_pos_left core (by positivity : (0:ℝ) < 8 * P.b)
      linarith
  · intro c hc0 hc
    have hbc : P.b * c < P.a * P.μ := by
      have := hbc_of c (lt_trans (lt_trans hc hCD) hDa)
      linarith
    have h1 : c * (P.b * (P.μ - P.α * t)) < P.a * P.α * P.μ * (1 - t) := by
      rw [← hCbar]; exact mul_lt_mul_of_pos_right hc hμαt
    have core := coreA_CS1 P.a P.b P.α P.μ t c _ hα0 ht0 ht2 hbc h1
    show (P.a * P.μ - P.b * c) ^ 2 * (P.α * (2 - P.α) * (1 - P.θ) + P.θ) /
        (32 * P.b * P.μ ^ 2) < (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2)
    apply fc2 _ _ _ _ (by positivity) (by positivity)
    have := mul_lt_mul_of_pos_left core (by positivity : (0:ℝ) < 32 * P.b)
    linarith
  · intro c hc hc2
    have hbc := hbc_of c (lt_trans hc2 hDa)
    have h1 : P.a * P.α * P.μ * (1 - t) < c * (P.b * (P.μ - P.α * t)) := by
      rw [← hCbar]; exact mul_lt_mul_of_pos_right hc hμαt
    have core := coreA_CS2 P.a P.b P.α P.μ t c _ hμpos ht2 hbc h1
    show (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2) <
      (P.a * P.μ - P.b * c) ^ 2 * (P.α * (2 - P.α) * (1 - P.θ) + P.θ) / (32 * P.b * P.μ ^ 2)
    apply fc2 _ _ _ _ (by positivity) (by positivity)
    have := mul_lt_mul_of_pos_left core (by positivity : (0:ℝ) < 32 * P.b)
    linarith

private lemma R_cmp (P : Params) (hP : P.Valid) (hα : (9 : ℝ) / 16 ≤ P.α) :
    cDR2 P < P.a * P.α / P.b ∧
    (∀ c, 0 < c → c < Ctil P →
      (OR2 P c).1 < (DR1 P c).1 ∧ (OR2 P c).2.1 < (DR1 P c).2.1 ∧
        (OR2 P c).2.2 < (DR1 P c).2.2) ∧
    (∀ c, Ctil P < c → c < P.a * P.α / P.b →
      (DR1 P c).1 < (OR2 P c).1 ∧ (DR1 P c).2.1 < (OR2 P c).2.1 ∧
        (DR1 P c).2.2 < (OR2 P c).2.2) ∧
    (∀ c, 0 < c → c < cDR2 P →
      (OR2 P c).1 < (DR2 P c).1 ∧ (DR2 P c).2.1 < (OR2 P c).2.1 ∧
        (OR2 P c).2.2 < (DR2 P c).2.2) := by
  obtain ⟨hμpos, hαμ, hμ1, hμ⟩ := base_facts P hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have h1θ : 0 < 1 - P.θ := by linarith
  have h1α : 0 < 1 - P.α := by linarith
  set D := P.α ^ 2 * (1 - P.θ) + P.θ with hD
  have hDpos : 0 < D := by positivity
  have hDα : P.α ^ 2 < D := by
    rw [hD]; nlinarith [mul_pos hθ0 (show 0 < 1 - P.α ^ 2 by nlinarith)]
  set u := Real.sqrt D with hu
  have hu2 : u ^ 2 = D := Real.sq_sqrt hDpos.le
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have huα : P.α < u := by
    rw [hu, Real.lt_sqrt hα0.le]; exact hDα
  clear_value u
  have hCtil : Ctil P * (P.b * (1 + P.α)) = P.a * P.α * (1 - u) := by
    have : Ctil P = P.a * P.α * (1 - u) / (P.b * (1 + P.α)) := by rw [hu, hD]; rfl
    rw [this]; field_simp
  -- base identity: u(aα - bc) - α(aμ - bc) = (u - α) b (Ctil - c)
  have hbase : ∀ c, u * (P.a * P.α - P.b * c) - P.α * (P.a * P.μ - P.b * c) =
      (u - P.α) * P.b * (Ctil P - c) := by
    intro c
    have h1a : (1 + P.α) ≠ 0 := by positivity
    apply mul_right_cancel₀ h1a
    rw [hD] at hu2
    rw [hμ]
    linear_combination (P.a * P.α) * hu2 - (u - P.α) * hCtil
  have hbc_of : ∀ c, c < P.a * P.α / P.b → P.b * c < P.a * P.α := by
    intro c hc
    rwa [lt_div_iff₀ hb, mul_comm] at hc
  have hαμ' : P.a * P.α < P.a * P.μ := mul_lt_mul_of_pos_left hαμ ha
  have hCt_lt : Ctil P < P.a * P.α / P.b := by
    have : Ctil P = P.a * P.α * (1 - u) / (P.b * (1 + P.α)) := by rw [hu, hD]; rfl
    rw [this, div_lt_div_iff₀ (by positivity) hb]
    have e : P.a * P.α * (P.b * (1 + P.α)) - P.a * P.α * (1 - u) * P.b =
        P.a * P.α * P.b * (P.α + u) := by ring
    have : 0 < P.a * P.α * P.b * (P.α + u) := by positivity
    linarith
  have hμθ : 0 < P.μ + P.θ := by linarith
  have hcDR2 : cDR2 P * (P.b * (P.μ + P.θ)) = P.a * P.α * P.μ * (1 - P.θ) := by
    unfold cDR2; field_simp
  have hDR2lt : cDR2 P < P.a * P.α / P.b := by
    unfold cDR2
    rw [div_lt_div_iff₀ (by positivity) hb]
    have e : P.a * P.α * (P.b * (P.μ + P.θ)) - P.a * P.α * P.μ * (1 - P.θ) * P.b =
        P.a * P.α * P.b * (P.θ * (1 + P.μ)) := by ring
    have : 0 < P.a * P.α * P.b * (P.θ * (1 + P.μ)) := by positivity
    linarith
  refine ⟨hDR2lt, ?_, ?_, ?_⟩
  · intro c hc0 hc
    have hbc := hbc_of c (lt_trans hc hCt_lt)
    have hb1 := hbase c
    have hpos : 0 < (u - P.α) * P.b * (Ctil P - c) := by
      have : 0 < u - P.α := by linarith
      have : 0 < Ctil P - c := by linarith
      positivity
    have key : P.α * (P.a * P.μ - P.b * c) < u * (P.a * P.α - P.b * c) := by linarith
    have hX : 0 ≤ P.α * (P.a * P.μ - P.b * c) := by
      have : 0 ≤ P.a * P.μ - P.b * c := by linarith
      positivity
    have hsq := sq_lt_sq_of _ _ hX key
    have core : P.α ^ 2 * (P.a * P.μ - P.b * c) ^ 2 < D * (P.b * c - P.a * P.α) ^ 2 := by
      have e1 : (P.α * (P.a * P.μ - P.b * c)) ^ 2 = P.α ^ 2 * (P.a * P.μ - P.b * c) ^ 2 := by
        ring
      have e2 : (u * (P.a * P.α - P.b * c)) ^ 2 = D * (P.b * c - P.a * P.α) ^ 2 := by
        rw [← hu2]; ring
      rw [e1, e2] at hsq; exact hsq
    refine ⟨?_, ?_, ?_⟩
    · show (P.a * P.μ - P.b * c) ^ 2 / (16 * P.b * D) <
        (P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2)
      apply fc2 _ _ _ _ (by positivity) (by positivity)
      have := mul_lt_mul_of_pos_left core (by positivity : (0:ℝ) < 16 * P.b)
      linarith
    · show (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * D) <
        (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2)
      apply fc2 _ _ _ _ (by positivity) (by positivity)
      have := mul_lt_mul_of_pos_left core (by positivity : (0:ℝ) < 8 * P.b)
      have e : (P.a * P.α - P.b * c) ^ 2 = (P.b * c - P.a * P.α) ^ 2 := by ring
      rw [e]; linarith
    · show (P.a * P.μ - P.b * c) ^ 2 / (32 * P.b * D) <
        (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2)
      apply fc2 _ _ _ _ (by positivity) (by positivity)
      have := mul_lt_mul_of_pos_left core (by positivity : (0:ℝ) < 32 * P.b)
      linarith
  · intro c hc hca
    have hbc := hbc_of c hca
    have hb1 := hbase c
    have hneg : (u - P.α) * P.b * (Ctil P - c) < 0 := by
      have : 0 < (u - P.α) * P.b := by
        have : 0 < u - P.α := by linarith
        positivity
      have : Ctil P - c < 0 := by linarith
      nlinarith
    have key : u * (P.a * P.α - P.b * c) < P.α * (P.a * P.μ - P.b * c) := by linarith
    have hX : 0 ≤ u * (P.a * P.α - P.b * c) := by
      have : 0 ≤ P.a * P.α - P.b * c := by linarith
      positivity
    have hsq := sq_lt_sq_of _ _ hX key
    have core : D * (P.b * c - P.a * P.α) ^ 2 < P.α ^ 2 * (P.a * P.μ - P.b * c) ^ 2 := by
      have e1 : (P.α * (P.a * P.μ - P.b * c)) ^ 2 = P.α ^ 2 * (P.a * P.μ - P.b * c) ^ 2 := by
        ring
      have e2 : (u * (P.a * P.α - P.b * c)) ^ 2 = D * (P.b * c - P.a * P.α) ^ 2 := by
        rw [← hu2]; ring
      rw [e1, e2] at hsq; exact hsq
    refine ⟨?_, ?_, ?_⟩
    · show (P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2) <
        (P.a * P.μ - P.b * c) ^ 2 / (16 * P.b * D)
      apply fc2 _ _ _ _ (by positivity) (by positivity)
      have := mul_lt_mul_of_pos_left core (by positivity : (0:ℝ) < 16 * P.b)
      linarith
    · show (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) <
        (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * D)
      apply fc2 _ _ _ _ (by positivity) (by positivity)
      have := mul_lt_mul_of_pos_left core (by positivity : (0:ℝ) < 8 * P.b)
      have e : (P.a * P.α - P.b * c) ^ 2 = (P.b * c - P.a * P.α) ^ 2 := by ring
      rw [e]; linarith
    · show (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2) <
        (P.a * P.μ - P.b * c) ^ 2 / (32 * P.b * D)
      apply fc2 _ _ _ _ (by positivity) (by positivity)
      have := mul_lt_mul_of_pos_left core (by positivity : (0:ℝ) < 32 * P.b)
      linarith
  · intro c hc0 hc
    have h1 : c * (P.b * (P.μ + P.θ)) < P.a * P.α * P.μ * (1 - P.θ) := by
      rw [← hcDR2]; exact mul_lt_mul_of_pos_right hc (by positivity)
    have hbc : P.b * c < P.a * P.α * (1 - P.θ) := by
      have : P.b * c * (P.μ + P.θ) < P.a * P.α * (1 - P.θ) * (P.μ + P.θ) := by
        have : P.a * P.α * P.μ * (1 - P.θ) < P.a * P.α * (1 - P.θ) * (P.μ + P.θ) := by
          have : 0 < P.a * P.α * (1 - P.θ) * P.θ := by positivity
          linarith
        linarith
      exact lt_of_mul_lt_mul_right this hμθ.le
    have hX : 0 ≤ P.α * (1 - P.θ) * (P.a * P.μ - P.b * c) := by
      have : 0 ≤ P.a * P.μ - P.b * c := by
        have : P.a * P.α * (1 - P.θ) ≤ P.a * P.μ := by
          have : P.α * (1 - P.θ) ≤ P.μ := by rw [hμ]; linarith
          have := mul_le_mul_of_nonneg_left this ha.le
          linarith
        linarith
      positivity
    have key : P.α * (1 - P.θ) * (P.a * P.μ - P.b * c) <
        2 * P.μ * (P.a * P.α * (1 - P.θ) - P.b * c) := by
      have e : 2 * P.μ * (P.a * P.α * (1 - P.θ) - P.b * c) -
          P.α * (1 - P.θ) * (P.a * P.μ - P.b * c) =
          P.a * P.α * P.μ * (1 - P.θ) - c * (P.b * (P.μ + P.θ)) := by
        rw [hμ]; ring
      linarith
    have hsq := sq_lt_sq_of _ _ hX key
    have core : P.α ^ 2 * (1 - P.θ) ^ 2 * (P.a * P.μ - P.b * c) ^ 2 <
        4 * (P.μ ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2) := by
      have e1 : (P.α * (1 - P.θ) * (P.a * P.μ - P.b * c)) ^ 2 =
          P.α ^ 2 * (1 - P.θ) ^ 2 * (P.a * P.μ - P.b * c) ^ 2 := by ring
      have e2 : (2 * P.μ * (P.a * P.α * (1 - P.θ) - P.b * c)) ^ 2 =
          4 * (P.μ ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2) := by ring
      rw [e1, e2] at hsq; exact hsq
    have gpos : 4 * P.b * P.μ * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) <
        P.α ^ 2 * (1 - P.θ) ^ 2 * (P.a * P.μ - P.b * c) ^ 2 := by
      have e : P.α ^ 2 * (1 - P.θ) ^ 2 * (P.a * P.μ - P.b * c) ^ 2 -
          4 * P.b * P.μ * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) =
          (P.a * P.α * P.μ * (1 - P.θ) - c * (P.b * (P.μ + P.θ))) ^ 2 := by
        rw [hμ]; ring
      have : 0 < (P.a * P.α * P.μ * (1 - P.θ) - c * (P.b * (P.μ + P.θ))) ^ 2 := by
        have : 0 < P.a * P.α * P.μ * (1 - P.θ) - c * (P.b * (P.μ + P.θ)) := by linarith
        positivity
      linarith
    refine ⟨?_, ?_, ?_⟩
    · show (P.a * P.μ - P.b * c) ^ 2 / (16 * P.b * D) <
        P.μ ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
          (4 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * D)
      apply fc2 _ _ _ _ (by positivity) (by positivity)
      have := mul_lt_mul_of_pos_left core (by positivity : (0:ℝ) < 4 * P.b * D)
      linarith
    · show P.μ * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
          (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * D) <
        (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * D)
      apply fc2 _ _ _ _ (by positivity) (by positivity)
      have := mul_lt_mul_of_pos_left gpos (by positivity : (0:ℝ) < 2 * D)
      linarith
    · show (P.a * P.μ - P.b * c) ^ 2 / (32 * P.b * D) <
        P.μ ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
          (8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * D)
      apply fc2 _ _ _ _ (by positivity) (by positivity)
      have := mul_lt_mul_of_pos_left core (by positivity : (0:ℝ) < 8 * P.b * D)
      linarith

theorem solution (P : Params) (hP : P.Valid) :
    (0 < Cbar P ∧ Cbar P < cDA P ∧
      (∀ c, costAdm P c →
        (∃ σ : Profile, IsSPE P c .OA σ) ∧
        (∃ σ : Profile, IsSPE P c .DA σ)) ∧
      (∀ c σOA σDA, costAdm P c →
        IsSPE P c .OA σOA → IsSPE P c .DA σDA →
        (max 0 (cOA2 P) < c ∧ c < max (Cbar P) (cOA2 P) →
          piR P c .OA σOA < piR P c .DA σDA ∧
          piS P c .OA σOA < piS P c .DA σDA ∧
          CS P c .OA σOA < CS P c .DA σDA) ∧
        (max (Cbar P) (cOA2 P) < c ∧ c < cDA P →
          piR P c .OA σOA < piR P c .DA σDA ∧
          piS P c .OA σOA < piS P c .DA σDA ∧
          CS P c .DA σDA < CS P c .OA σOA) ∧
        ((c < max 0 (cOA1 P)) ∨ (cDA P < c) →
          piR P c .OA σOA = piR P c .DA σDA ∧
          piS P c .OA σOA = piS P c .DA σDA ∧
          CS P c .OA σOA = CS P c .DA σDA))) ∧
    ((9 : ℝ) / 16 ≤ P.α →
      (∀ c, costAdm P c →
        (∃ σ : Profile, IsSPE P c .OR σ) ∧
        (∃ σ : Profile, IsSPE P c .DR σ)) ∧
      (∀ c σOR σDR, costAdm P c →
        IsSPE P c .OR σOR → IsSPE P c .DR σDR →
        (c < Ctil P →
          piR P c .OR σOR < piR P c .DR σDR ∧
          piS P c .OR σOR < piS P c .DR σDR ∧
          CS P c .OR σOR < CS P c .DR σDR) ∧
        (Ctil P < c ∧ c < cDR1 P →
          piR P c .DR σDR < piR P c .OR σOR ∧
          piS P c .DR σDR < piS P c .OR σOR ∧
          CS P c .DR σDR < CS P c .OR σOR) ∧
        (cDR1 P < c ∧ c < cDR2 P →
          piR P c .OR σOR < piR P c .DR σDR ∧
          piS P c .DR σDR < piS P c .OR σOR ∧
          CS P c .OR σOR < CS P c .DR σDR) ∧
        (cDR2 P < c →
          piR P c .OR σOR = piR P c .DR σDR ∧
          piS P c .OR σOR = piS P c .DR σDR ∧
          CS P c .OR σOR = CS P c .DR σDR))) := by
  have L1 := YieldPostpone.Payment.lemma_1_corrected P hP
  have L3 := YieldPostpone.Payment.lemma_3 P hP
  have OT := YieldPostpone.Payment.oa_threshold_order P hP
  obtain ⟨hC0, hCD, hA1, hA2, hA3⟩ := A_cmp P hP
  refine ⟨⟨hC0, hCD, fun c hc => ⟨(L1.2.2 c hc).1, (L3 c hc).1⟩, ?_⟩, fun hα => ?_⟩
  · intro c σOA σDA hc hOA hDA
    have o1 := (L1.2.2 c hc).2 σOA hOA
    have o3 := (L3 c hc).2 σDA hDA
    have hc0 : 0 < c := hc.1
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨h1, h2⟩
      have hc2 : cOA2 P < c := lt_of_le_of_lt (le_max_right _ _) h1
      have hcC : c < Cbar P := by
        by_contra h
        push Not at h
        have : max (Cbar P) (cOA2 P) ≤ c := max_le h hc2.le
        linarith
      have hcD : c < cDA P := lt_trans hcC hCD
      have eO := o1.2.2 h1
      have eD := o3.1 hcD
      obtain ⟨r1, r2⟩ := hA1 c hc0 hcD
      have r3 := hA2 c hc0 hcC
      have a1 : piR P c .OA σOA = (OA3 P c).1 := congrArg Prod.fst eO
      have a2 : piR P c .DA σDA = (DA1 P c).1 := congrArg Prod.fst eD
      have b1 : piS P c .OA σOA = (OA3 P c).2.1 := congrArg (fun x => x.2.1) eO
      have b2 : piS P c .DA σDA = (DA1 P c).2.1 := congrArg (fun x => x.2.1) eD
      have d1 : CS P c .OA σOA = (OA3 P c).2.2 := congrArg (fun x => x.2.2) eO
      have d2 : CS P c .DA σDA = (DA1 P c).2.2 := congrArg (fun x => x.2.2) eD
      rw [a1, a2, b1, b2, d1, d2]
      exact ⟨r1, r2, r3⟩
    · rintro ⟨h1, h2⟩
      have hc2 : cOA2 P < c := lt_of_le_of_lt (le_max_right _ _) h1
      have hcC : Cbar P < c := lt_of_le_of_lt (le_max_left _ _) h1
      have h0 : max 0 (cOA2 P) < c := max_lt hc0 hc2
      have eO := o1.2.2 h0
      have eD := o3.1 h2
      obtain ⟨r1, r2⟩ := hA1 c hc0 h2
      have r3 := hA3 c hcC h2
      have a1 : piR P c .OA σOA = (OA3 P c).1 := congrArg Prod.fst eO
      have a2 : piR P c .DA σDA = (DA1 P c).1 := congrArg Prod.fst eD
      have b1 : piS P c .OA σOA = (OA3 P c).2.1 := congrArg (fun x => x.2.1) eO
      have b2 : piS P c .DA σDA = (DA1 P c).2.1 := congrArg (fun x => x.2.1) eD
      have d1 : CS P c .OA σOA = (OA3 P c).2.2 := congrArg (fun x => x.2.2) eO
      have d2 : CS P c .DA σDA = (DA1 P c).2.2 := congrArg (fun x => x.2.2) eD
      rw [a1, a2, b1, b2, d1, d2]
      exact ⟨r1, r2, r3⟩
    · intro h
      have heq : outcome P c .OA σOA = outcome P c .DA σDA := by
        rcases h with h | h
        · have hc1 : cOA1 P < c ∨ c < cOA1 P := by
            rcases lt_or_ge c (cOA1 P) with h' | h'
            · exact Or.inr h'
            · exfalso
              have : max 0 (cOA1 P) ≤ c := max_le hc0.le h'
              linarith
          have hc1' : c < cOA1 P := by
            rcases hc1 with h' | h'
            · exfalso
              have : max 0 (cOA1 P) ≤ c := max_le hc0.le h'.le
              linarith
            · exact h'
          have hcD : c < cDA P := lt_trans hc1' (lt_trans OT.1 OT.2)
          rw [o1.1 h, o3.1 hcD]
          have e : (P.a * P.α - P.b * c) ^ 2 = (P.b * c - P.a * P.α) ^ 2 := by ring
          simp only [OA1, DA1, e]
        · have h0 : max 0 (cOA2 P) < c := max_lt hc0 (lt_trans OT.2 h)
          rw [o1.2.2 h0, o3.2 h]
          have e : (P.b * c - P.a * P.μ) ^ 2 = (P.a * P.μ - P.b * c) ^ 2 := by ring
          simp only [OA3, DA2, e]
      refine ⟨congrArg Prod.fst heq, congrArg (fun x => x.2.1) heq,
        congrArg (fun x => x.2.2) heq⟩
  · have L2 := YieldPostpone.Payment.lemma_2 P hP
    have L4 := YieldPostpone.Payment.lemma_4 P hP hα
    obtain ⟨hcOR, hCt0, hCt1, hDR12⟩ := YieldPostpone.Payment.responsive_threshold_order P hP hα
    obtain ⟨hDR2a, hR1, hR2, hR3⟩ := R_cmp P hP hα
    refine ⟨fun c hc => ⟨(L2.2 c hc).1, (L4 c hc).1⟩, ?_⟩
    intro c σOR σDR hc hOR hDR
    have hc0 : 0 < c := hc.1
    have eO : outcome P c .OR σOR = OR2 P c :=
      ((L2.2 c hc).2 σOR hOR).2 (by rw [max_eq_left hcOR.le]; exact hc0)
    have o4 := (L4 c hc).2 σDR hDR
    have a1 : piR P c .OR σOR = (OR2 P c).1 := congrArg Prod.fst eO
    have b1 : piS P c .OR σOR = (OR2 P c).2.1 := congrArg (fun x => x.2.1) eO
    have d1 : CS P c .OR σOR = (OR2 P c).2.2 := congrArg (fun x => x.2.2) eO
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      have eD := o4.1 (lt_trans h hCt1)
      have a2 : piR P c .DR σDR = (DR1 P c).1 := congrArg Prod.fst eD
      have b2 : piS P c .DR σDR = (DR1 P c).2.1 := congrArg (fun x => x.2.1) eD
      have d2 : CS P c .DR σDR = (DR1 P c).2.2 := congrArg (fun x => x.2.2) eD
      rw [a1, a2, b1, b2, d1, d2]
      exact hR1 c hc0 h
    · rintro ⟨h1, h2⟩
      have eD := o4.1 h2
      have a2 : piR P c .DR σDR = (DR1 P c).1 := congrArg Prod.fst eD
      have b2 : piS P c .DR σDR = (DR1 P c).2.1 := congrArg (fun x => x.2.1) eD
      have d2 : CS P c .DR σDR = (DR1 P c).2.2 := congrArg (fun x => x.2.2) eD
      rw [a1, a2, b1, b2, d1, d2]
      exact hR2 c h1 (lt_trans (lt_trans h2 hDR12) hDR2a)
    · rintro ⟨h1, h2⟩
      have eD := o4.2.1 ⟨h1, h2⟩
      have a2 : piR P c .DR σDR = (DR2 P c).1 := congrArg Prod.fst eD
      have b2 : piS P c .DR σDR = (DR2 P c).2.1 := congrArg (fun x => x.2.1) eD
      have d2 : CS P c .DR σDR = (DR2 P c).2.2 := congrArg (fun x => x.2.2) eD
      rw [a1, a2, b1, b2, d1, d2]
      exact hR3 c hc0 h2
    · intro h
      have eD := o4.2.2 h
      have a2 : piR P c .DR σDR = (DR3 P c).1 := congrArg Prod.fst eD
      have b2 : piS P c .DR σDR = (DR3 P c).2.1 := congrArg (fun x => x.2.1) eD
      have d2 : CS P c .DR σDR = (DR3 P c).2.2 := congrArg (fun x => x.2.2) eD
      rw [a1, a2, b1, b2, d1, d2]
      exact ⟨rfl, rfl, rfl⟩

