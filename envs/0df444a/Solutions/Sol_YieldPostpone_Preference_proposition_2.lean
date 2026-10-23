-- Prove2me | solution 1 for YieldPostpone.Preference.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T05:33:41.540254+00:00
-- url     : https://prove2.me/submissions/32f5896c-2ac4-4eef-8a3c-6adc09cd306f

import Mathlib
import Definitions.Def_YieldPostpone_Preference_Setting
import Theorems.Thm_YieldPostpone_Preference_lemma_2
import Theorems.Thm_YieldPostpone_Preference_lemma_3
import Theorems.Thm_YieldPostpone_Preference_lemma_3_at_cDA
import Theorems.Thm_YieldPostpone_Preference_lemma_4
import Theorems.Thm_YieldPostpone_Preference_threshold_order
import Theorems.Thm_YieldPostpone_Preference_Ctil_mem

open YieldPostpone.Preference

namespace Prop2Aux

/-- Squared comparison: `0 ≤ x`, `x < y` gives `x² < y²`. -/
lemma sq_lt_sq_of (x y : ℝ) (hx : 0 ≤ x) (h : x < y) : x ^ 2 < y ^ 2 := by
  nlinarith

/-- `OR2 < DA1` ⇔ `α(aμ−bc) < s(aα−bc)` after squaring (`s² = K`). -/
lemma cmp_OR_DA1 (a b α μ K s c : ℝ) (hb : 0 < b) (hα : 0 < α) (hK : 0 < K) (hs : s ^ 2 = K)
    (h0 : 0 ≤ α * (a * μ - b * c)) (h : α * (a * μ - b * c) < s * (a * α - b * c)) :
    (a * μ - b * c) ^ 2 / (16 * b * K) < (b * c - a * α) ^ 2 / (16 * b * α ^ 2) := by
  have h2 := sq_lt_sq_of _ _ h0 h
  rw [mul_pow, mul_pow, hs] at h2
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have e : (b * c - a * α) ^ 2 = (a * α - b * c) ^ 2 := by ring
  rw [e]
  nlinarith [mul_lt_mul_of_pos_left h2 (show (0:ℝ) < 16 * b by positivity)]

lemma cmp_DA1_OR (a b α μ K s c : ℝ) (hb : 0 < b) (hα : 0 < α) (hK : 0 < K) (hs : s ^ 2 = K)
    (h0 : 0 ≤ s * (a * α - b * c)) (h : s * (a * α - b * c) < α * (a * μ - b * c)) :
    (b * c - a * α) ^ 2 / (16 * b * α ^ 2) < (a * μ - b * c) ^ 2 / (16 * b * K) := by
  have h2 := sq_lt_sq_of _ _ h0 h
  rw [mul_pow, mul_pow, hs] at h2
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have e : (b * c - a * α) ^ 2 = (a * α - b * c) ^ 2 := by ring
  rw [e]
  nlinarith [mul_lt_mul_of_pos_left h2 (show (0:ℝ) < 16 * b by positivity)]

lemma cmp_OR_DRm (a b α θ μ K c : ℝ) (hb : 0 < b) (hα : 0 < α) (hθ : θ < 1) (hK : 0 < K)
    (h0 : 0 ≤ α * (1 - θ) * (a * μ - b * c))
    (h : α * (1 - θ) * (a * μ - b * c) < 2 * μ * (a * α * (1 - θ) - b * c)) :
    (a * μ - b * c) ^ 2 / (16 * b * K) <
      μ ^ 2 * (a * α * (1 - θ) - b * c) ^ 2 / (4 * b * α ^ 2 * (1 - θ) ^ 2 * K) := by
  have h2 := sq_lt_sq_of _ _ h0 h
  have h1θ : 0 < 1 - θ := by linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hpos : 0 < 4 * b * K := by positivity
  have := mul_lt_mul_of_pos_left h2 hpos
  nlinarith [this]

lemma cmp_DA2_OR (a b μ K c : ℝ) (hb : 0 < b) (hK : 0 < K) (hKμ : K < μ) (hc : b * c < a * μ) :
    (b * c - a * μ) ^ 2 / (16 * b * μ) < (a * μ - b * c) ^ 2 / (16 * b * K) := by
  have hμ : 0 < μ := lt_trans hK hKμ
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hx : 0 < (a * μ - b * c) ^ 2 := by
    have : 0 < a * μ - b * c := by linarith
    positivity
  have e : (b * c - a * μ) ^ 2 = (a * μ - b * c) ^ 2 := by ring
  rw [e]
  have := mul_lt_mul_of_pos_left hKμ (show 0 < (a * μ - b * c) ^ 2 * (16 * b) by positivity)
  nlinarith [this]

end Prop2Aux

open Prop2Aux in
theorem solution (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    (∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
        (∃ σ : Profile, IsSPE P c .OR σ) ∧ (∃ σ : Profile, IsSPE P c .DA σ) ∧
          (∃ σ : Profile, IsSPE P c .DR σ)) ∧
    ∀ (c : ℝ) (σOR σDA σDR : Profile), 0 < c → c < P.a * μ P / P.b →
      IsSPE P c .OR σOR → IsSPE P c .DA σDA → IsSPE P c .DR σDR →
      (c < Ctil P →
          piR P c .OR σOR < piR P c .DR σDR ∧ piR P c .DR σDR = piR P c .DA σDA) ∧
      (Ctil P < c → c < cDR1 P →
          piR P c .DA σDA = piR P c .DR σDR ∧ piR P c .DR σDR < piR P c .OR σOR) ∧
      (cDR1 P < c → c < cDR2 P →
          piR P c .DA σDA < piR P c .OR σOR ∧ piR P c .OR σOR < piR P c .DR σDR) ∧
      (cDR2 P < c →
          piR P c .DA σDA < piR P c .DR σDR ∧ piR P c .DR σDR = piR P c .OR σOR) := by
  obtain ⟨-, L2e, -, L2b⟩ := lemma_2 P hP
  obtain ⟨L3e, L3a, L3b⟩ := lemma_3 P hP
  have L3c := lemma_3_at_cDA P hP
  obtain ⟨L4e, L4a, L4b, L4c⟩ := lemma_4 P hP hα
  obtain ⟨hOR, hD12, hD2A⟩ := threshold_order P hP hα
  obtain ⟨hCt0, hCt1⟩ := Ctil_mem P hP hα
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  set K := P.α ^ 2 * (1 - P.θ) + P.θ with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  have hKμ : K < μ P := by
    rw [hK, hμ]; nlinarith [mul_pos (mul_pos hα0 (show 0 < 1 - P.α by linarith)) h1θ]
  have hKα : P.α ^ 2 < K := by rw [hK]; nlinarith [mul_pos (show 0 < 1 - P.α ^ 2 by nlinarith) hθ0]
  set s := Real.sqrt K with hsd
  have hs2 : s ^ 2 = K := Real.sq_sqrt hK0.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsα : P.α < s := by nlinarith
  -- linear identity behind `C̃`
  have hCtil : ∀ c, s * (P.a * P.α - P.b * c) - P.α * (P.a * μ P - P.b * c) =
      P.b * (s - P.α) * (Ctil P - c) := by
    intro c
    have hC : Ctil P = P.a * P.α * (1 - s) / (P.b * (1 + P.α)) := rfl
    have hCb : Ctil P * (P.b * (1 + P.α)) = P.a * P.α * (1 - s) := by
      rw [hC]; exact div_mul_cancel₀ _ (by positivity)
    have hs2' : s ^ 2 = P.α ^ 2 * (1 - P.θ) + P.θ := hs2.trans hK
    have h : (1 + P.α) * ((s * (P.a * P.α - P.b * c) - P.α * (P.a * μ P - P.b * c)) -
        P.b * (s - P.α) * (Ctil P - c)) = 0 := by
      rw [hμ]; linear_combination (-(s - P.α)) * hCb + (P.a * P.α) * hs2'
    have h1α : (1 + P.α) ≠ 0 := by positivity
    have := (mul_eq_zero.mp h).resolve_left h1α
    linarith
  -- linear identity behind `c^DR_2`
  have hDR2 : ∀ c, 2 * μ P * (P.a * P.α * (1 - P.θ) - P.b * c) - P.α * (1 - P.θ) * (P.a * μ P - P.b * c) =
      P.b * (μ P + P.θ) * (cDR2 P - c) := by
    intro c
    have hC : cDR2 P = P.a * P.α * μ P * (1 - P.θ) / (P.b * (μ P + P.θ)) := rfl
    rw [hC]
    field_simp
    rw [hμ]; ring
  -- `c^DA < aα/b`
  have hDAa : cDA P < P.a * P.α / P.b := by
    have hC : cDA P = P.a * P.α * (μ P - P.θ * Real.sqrt (μ P)) / (P.b * (P.α + P.θ)) := rfl
    rw [hC, div_lt_div_iff₀ (by positivity) hb]
    have : 0 ≤ P.θ * Real.sqrt (μ P) := by positivity
    have h1 : μ P - P.θ * Real.sqrt (μ P) < P.α + P.θ := by
      rw [hμ] at this ⊢; nlinarith [mul_pos hα0 hθ0]
    have := mul_lt_mul_of_pos_left h1 (show 0 < P.a * P.α * P.b by positivity)
    nlinarith
  -- values of the comparisons
  have OR_lt_DA1 : ∀ c, c < Ctil P → P.b * c < P.a * μ P →
      (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * K) < (P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2) := by
    intro c hc hcu
    apply cmp_OR_DA1 _ _ _ _ _ s _ hb hα0 hK0 hs2
    · have : 0 ≤ P.a * μ P - P.b * c := by linarith
      positivity
    · have := hCtil c
      have : 0 < P.b * (s - P.α) * (Ctil P - c) := by
        apply mul_pos (mul_pos hb (by linarith)) (by linarith)
      linarith
  have DA1_lt_OR : ∀ c, Ctil P < c → c < cDA P →
      (P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2) < (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * K) := by
    intro c hc hcu
    apply cmp_DA1_OR _ _ _ _ _ s _ hb hα0 hK0 hs2
    · have : 0 ≤ P.a * P.α - P.b * c := by
        have := lt_trans hcu hDAa
        rw [lt_div_iff₀ hb] at this; linarith
      positivity
    · have := hCtil c
      have : P.b * (s - P.α) * (Ctil P - c) < 0 := by
        apply mul_neg_of_pos_of_neg (mul_pos hb (by linarith)) (by linarith)
      linarith
  refine ⟨fun c hc hcu => ⟨L2e c hc hcu, L3e c hc hcu, L4e c hc hcu⟩, ?_⟩
  intro c σOR σDA σDR hc hcu hOR' hDA' hDR'
  have hbc : P.b * c < P.a * μ P := by rw [lt_div_iff₀ hb] at hcu; linarith
  have hmax : max 0 (cOR P) < c := by rw [max_eq_left hOR.le]; exact hc
  have vOR := (L2b c σOR hmax hcu hOR').1
  refine ⟨fun h1 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 => ?_⟩
  · have vDR := (L4a c σDR hc (by linarith) hDR').1
    have vDA := (L3a c σDA hc (by linarith) hDA').1
    rw [vOR, vDR, vDA]
    exact ⟨OR_lt_DA1 c h1 hbc, rfl⟩
  · have vDR := (L4a c σDR hc h2 hDR').1
    have vDA := (L3a c σDA hc (by linarith) hDA').1
    rw [vOR, vDR, vDA]
    exact ⟨rfl, DA1_lt_OR c h1 (by linarith)⟩
  · have vDR := (L4b c σDR h1 h2 hDR').1
    have vDA := (L3a c σDA hc (by linarith) hDA').1
    rw [vOR, vDR, vDA]
    refine ⟨DA1_lt_OR c (by linarith) (by linarith), ?_⟩
    apply cmp_OR_DRm _ _ _ _ _ _ _ hb hα0 hθ1 hK0
    · have : 0 ≤ P.a * μ P - P.b * c := by linarith
      positivity
    · have := hDR2 c
      have : 0 < P.b * (μ P + P.θ) * (cDR2 P - c) := by
        apply mul_pos (mul_pos hb (by linarith)) (by linarith)
      linarith
  · have vDR := (L4c c σDR h1 hcu hDR').1
    rw [vOR, vDR]
    refine ⟨?_, rfl⟩
    rcases lt_trichotomy c (cDA P) with hlt | heq | hgt
    · rw [(L3a c σDA hc hlt hDA').1]
      exact DA1_lt_OR c (by linarith) hlt
    · subst heq
      rw [(L3c σDA hDA').1]
      exact cmp_DA2_OR _ _ _ _ _ hb hK0 hKμ hbc
    · rw [(L3b c σDA hgt hcu hDA').1]
      exact cmp_DA2_OR _ _ _ _ _ hb hK0 hKμ hbc
