-- Prove2me | solution 1 for YieldPostpone.Interplay.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T02:41:08.146681+00:00
-- url     : https://prove2.me/submissions/aace559f-df92-430a-abc6-db3186cc0fd2

import Mathlib
import Theorems.Thm_YieldPostpone_Interplay_lemma_1
import Theorems.Thm_YieldPostpone_Interplay_lemma_1_i
import Theorems.Thm_YieldPostpone_Interplay_lemma_2
import Theorems.Thm_YieldPostpone_Interplay_lemma_3
import Theorems.Thm_YieldPostpone_Interplay_lemma_4
import Theorems.Thm_YieldPostpone_Interplay_lemma_4_at_cDR2
import Theorems.Thm_YieldPostpone_Interplay_threshold_order
import Definitions.Def_YieldPostpone_Interplay_Interaction
import Theorems.Thm_YieldPostpone_Interplay_interaction_mid_cDR1_pos

namespace YP3Alg2

noncomputable def F (α θ x : ℝ) : ℝ :=
  (α*(1-θ)+θ)^2*(α*(1-θ)-x)^2/(4*α^2*(1-θ)^2*(α^2*(1-θ)+θ)) - ((α*(1-θ)+θ)-x)^2/(16*(α^2*(1-θ)+θ))
    - (α-x)^2/(16*α^2) + ((α*(1-θ)+θ)-x)^2/(16*(α*(1-θ)+θ))

lemma F_x2 (α θ : ℝ) (h2 : 0 < α) (h3 : 0 < θ) (h4 : θ < 1) :
    F α θ (α*(α*(1-θ)+θ)*(1-θ)/((α*(1-θ)+θ)+θ)) = -(θ^2*(1-(α*(1-θ)+θ))^2)/(16*((α*(1-θ)+θ)+θ)^2) := by
  have hθ1 : (1-θ) ≠ 0 := by linarith
  have hμ : 0 < α*(1-θ)+θ := by nlinarith
  have hs : 0 < α^2*(1-θ)+θ := by nlinarith
  unfold F
  field_simp
  ring

end YP3Alg2

namespace YP3Alg2

lemma F_quad (α θ x y : ℝ) (h2 : 0 < α) (h3 : 0 < θ) (h4 : θ < 1) :
    F α θ x - F α θ y = (x - y) * (((α*(1-θ)+θ)^2/(4*α^2*(1-θ)^2*(α^2*(1-θ)+θ)) - 1/(16*(α^2*(1-θ)+θ))
        - 1/(16*α^2) + 1/(16*(α*(1-θ)+θ))) * (x + y)
      + (-2*α*(1-θ)*(α*(1-θ)+θ)^2/(4*α^2*(1-θ)^2*(α^2*(1-θ)+θ)) + 2*(α*(1-θ)+θ)/(16*(α^2*(1-θ)+θ))
        + 2*α/(16*α^2) - 2*(α*(1-θ)+θ)/(16*(α*(1-θ)+θ)))) := by
  have hθ1 : (1-θ) ≠ 0 := by linarith
  have hμ : 0 < α*(1-θ)+θ := by nlinarith
  have hs : 0 < α^2*(1-θ)+θ := by nlinarith
  have := hμ.ne'; have := hs.ne'; have := h2.ne'
  unfold F
  field_simp
  ring

lemma Lc_pos (α θ : ℝ) (h1 : 9 / 16 ≤ α) (h2 : α < 1) (h3 : 0 < θ) (h4 : θ < 1) :
    0 < (α*(1-θ)+θ)^2/(4*α^2*(1-θ)^2*(α^2*(1-θ)+θ)) - 1/(16*(α^2*(1-θ)+θ))
        - 1/(16*α^2) + 1/(16*(α*(1-θ)+θ)) := by
  have ha0 : 0 < α := by linarith
  have hθ' : 0 < 1 - θ := by linarith
  have hμ : 0 < α*(1-θ)+θ := by nlinarith
  have hs : 0 < α^2*(1-θ)+θ := by nlinarith
  set μ := α*(1-θ)+θ with hμd
  set s := α^2*(1-θ)+θ with hsd
  have hu : α*(1-θ) ≤ μ := by rw [hμd]; linarith
  have hsm : (1-θ)^2*s ≤ μ^2 := by
    rw [hsd, hμd]; nlinarith [mul_pos h3 hθ', mul_pos (mul_pos h3 hθ') hθ', sq_nonneg (1-θ)]
  have hN : 0 < 4*μ^3 - α^2*(1-θ)^2*μ - (1-θ)^2*s*μ + α^2*(1-θ)^2*s := by
    have e1 : α^2*(1-θ)^2*μ ≤ μ^3 := by
      have : (α*(1-θ))^2 ≤ μ^2 := by apply pow_le_pow_left₀ (by positivity) hu
      nlinarith
    have e2 : (1-θ)^2*s*μ ≤ μ^3 := by nlinarith
    have : 0 < μ^3 := by positivity
    have : 0 ≤ α^2*(1-θ)^2*s := by positivity
    linarith
  have e : μ^2/(4*α^2*(1-θ)^2*s) - 1/(16*s) - 1/(16*α^2) + 1/(16*μ)
      = (4*μ^3 - α^2*(1-θ)^2*μ - (1-θ)^2*s*μ + α^2*(1-θ)^2*s)/(16*α^2*(1-θ)^2*s*μ) := by
    field_simp
    ring
  rw [e]; positivity

lemma sign_pattern (α θ x1 x2 : ℝ) (h1 : 9 / 16 ≤ α) (h2 : α < 1) (h3 : 0 < θ) (h4 : θ < 1)
    (h12 : x1 < x2) (hf1 : 0 < F α θ x1) (hf2 : F α θ x2 < 0) :
    ∃ r, x1 < r ∧ r < x2 ∧ (∀ x, x1 < x → x < r → 0 < F α θ x) ∧
      (∀ x, r < x → x < x2 → F α θ x < 0) := by
  have ha0 : 0 < α := by linarith
  have hcont : ContinuousOn (F α θ) (Set.Icc x1 x2) := by
    apply Continuous.continuousOn
    unfold F
    fun_prop
  obtain ⟨r, ⟨hr1, hr2⟩, hr⟩ := intermediate_value_Ioo' h12.le hcont ⟨hf2, hf1⟩
  have hL := Lc_pos α θ h1 h2 h3 h4
  set Lc := (α*(1-θ)+θ)^2/(4*α^2*(1-θ)^2*(α^2*(1-θ)+θ)) - 1/(16*(α^2*(1-θ)+θ))
        - 1/(16*α^2) + 1/(16*(α*(1-θ)+θ)) with hLd
  set Bc := (-2*α*(1-θ)*(α*(1-θ)+θ)^2/(4*α^2*(1-θ)^2*(α^2*(1-θ)+θ)) + 2*(α*(1-θ)+θ)/(16*(α^2*(1-θ)+θ))
        + 2*α/(16*α^2) - 2*(α*(1-θ)+θ)/(16*(α*(1-θ)+θ))) with hBd
  have hq : ∀ x, F α θ x = (x - r) * (Lc * (x + r) + Bc) := by
    intro x
    have := F_quad α θ x r ha0 h3 h4
    rw [hr] at this
    linarith
  have hK2 : Lc * (x2 + r) + Bc < 0 := by
    have := hq x2
    by_contra hc
    rw [not_lt] at hc
    have : 0 ≤ (x2 - r) * (Lc * (x2 + r) + Bc) := mul_nonneg (by linarith) hc
    linarith
  refine ⟨r, hr1, hr2, ?_, ?_⟩
  · intro x hx1 hxr
    rw [hq x]
    have : Lc * (x + r) + Bc < 0 := by nlinarith
    nlinarith
  · intro x hrx hx2
    rw [hq x]
    have : Lc * (x + r) + Bc < 0 := by nlinarith
    nlinarith

end YP3Alg2

open YieldPostpone.Interplay YP3Alg2

lemma yp3_mid (a b α θ c : ℝ) (ha : 0 < a) (hb : 0 < b) (h2 : 0 < α) (h3 : 0 < θ) (h4 : θ < 1) :
    (α*(1-θ)+θ)^2*(a*α*(1-θ)-b*c)^2/(4*b*α^2*(1-θ)^2*(α^2*(1-θ)+θ))
      - (a*(α*(1-θ)+θ)-b*c)^2/(16*b*(α^2*(1-θ)+θ))
      - ((b*c-a*α)^2/(16*b*α^2) - (a*(α*(1-θ)+θ)-b*c)^2/(16*b*(α*(1-θ)+θ)))
      = a^2/b * F α θ (b*c/a) := by
  have hθ1 : (1-θ) ≠ 0 := by linarith
  have hμ : 0 < α*(1-θ)+θ := by nlinarith
  have hs : 0 < α^2*(1-θ)+θ := by nlinarith
  have := hμ.ne'; have := hs.ne'; have := h2.ne'; have := ha.ne'; have := hb.ne'
  unfold F
  field_simp
  ring

lemma yp3_AOA (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (hcA : c < cDA P)
    (hcμ : P.b * c < P.a * μ P) :
    (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * μ P) < (P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ0 : 0 < μ P := by unfold μ; nlinarith
  have hμ1 : μ P < 1 := by unfold μ; nlinarith
  have hαμ : P.α < μ P := by unfold μ; nlinarith
  set m := Real.sqrt (μ P) with hmd
  have hm2 : m ^ 2 = μ P := Real.sq_sqrt hμ0.le
  have hμm : μ P < m := by rw [hmd, Real.lt_sqrt hμ0.le]; nlinarith
  have hQ1 : P.b * cDA P * (P.α + P.θ) = P.a * P.α * (μ P - P.θ * m) := by
    unfold cDA; rw [← hmd]; field_simp
  have hG : (m * (P.a * P.α - P.b * c) - P.α * (P.a * μ P - P.b * c)) * (P.α + P.θ)
      = P.b * (m - P.α) * (cDA P - c) * (P.α + P.θ) := by
    have hμdef : μ P = P.α * (1 - P.θ) + P.θ := rfl
    linear_combination (-(m - P.α)) * hQ1 + (P.a * P.α * P.θ) * hm2 + (-(P.a * P.α * m)) * hμdef
  have hpos : 0 < P.b * (m - P.α) * (cDA P - c) * (P.α + P.θ) := by
    have : 0 < m - P.α := by linarith
    have : 0 < cDA P - c := by linarith
    positivity
  have hG' : P.α * (P.a * μ P - P.b * c) < m * (P.a * P.α - P.b * c) := by
    rw [← hG] at hpos
    have hαθ : 0 < P.α + P.θ := by linarith
    nlinarith
  have h0 : 0 < P.α * (P.a * μ P - P.b * c) := by nlinarith
  have hsq : (P.α * (P.a * μ P - P.b * c)) ^ 2 < (m * (P.a * P.α - P.b * c)) ^ 2 := by
    apply pow_lt_pow_left₀ hG' h0.le (by norm_num)
  have hsq' : P.α ^ 2 * (P.a * μ P - P.b * c) ^ 2 < μ P * (P.b * c - P.a * P.α) ^ 2 := by
    have e1 : (m * (P.a * P.α - P.b * c)) ^ 2 = μ P * (P.b * c - P.a * P.α) ^ 2 := by
      rw [mul_pow, hm2]; ring
    nlinarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

set_option maxHeartbeats 2000000 in
theorem solution (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) (hH : H3 P.α P.θ) :
    (∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
      (∃ σ : Profile, IsSPE P c .OA σ) ∧ (∃ σ : Profile, IsSPE P c .OR σ) ∧
      (∃ σ : Profile, IsSPE P c .DA σ) ∧ (∃ σ : Profile, IsSPE P c .DR σ)) ∧
    ∃ Chat : ℝ, 0 < Chat ∧ Chat < P.a * μ P / P.b ∧
      ∀ (c : ℝ) (σOA σOR σDA σDR : Profile), 0 < c → c < P.a * μ P / P.b →
        IsSPE P c .OA σOA → IsSPE P c .OR σOR → IsSPE P c .DA σDA → IsSPE P c .DR σDR →
        ((c < cDR1 P ∨ (Chat < c ∧ c < cDA P)) → interaction P c σOA σOR σDA σDR < 0) ∧
        (cDR1 P < c → c < Chat → 0 < interaction P c σOA σOR σDA σDR) ∧
        (cDA P < c → interaction P c σOA σOR σDA σDR = 0) := by
  have hP0 := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP0
  obtain ⟨_, _, hL1⟩ := lemma_1 P hP
  have hOA2 : cOA2 P ≤ 0 := (lemma_1_i P hP).2.2 hH
  obtain ⟨_, hL2⟩ := lemma_2 P hP
  have hL3 := lemma_3 P hP
  have hL4 := lemma_4 P hP hα
  have hL4' := lemma_4_at_cDR2 P hP hα
  obtain ⟨hORn, h12, h2A⟩ := threshold_order P hP hα
  have hθ' : 0 < 1 - P.θ := by linarith
  have hμ0 : 0 < μ P := by unfold μ; nlinarith
  have hs0 : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by nlinarith
  have hsμ : P.α ^ 2 * (1 - P.θ) + P.θ < μ P := by
    unfold μ; nlinarith [mul_pos (mul_pos hα0 (sub_pos.mpr hα1)) hθ']
  have hD : 0 < P.α^2*(1-P.θ)^3+4*P.α*P.θ*(1-P.θ)+P.θ*(1+P.θ)^2 := by positivity
  -- normalized thresholds
  set X1 := P.α*(1-P.θ)*((P.α*(1-P.θ)+P.θ)^2+P.θ-2*P.θ*Real.sqrt (P.α*(P.α*(1-P.θ)+P.θ)*(1-P.α)*(1-P.θ)))/(P.α^2*(1-P.θ)^3+4*P.α*P.θ*(1-P.θ)+P.θ*(1+P.θ)^2) with hX1
  set X2 := P.α*(P.α*(1-P.θ)+P.θ)*(1-P.θ)/((P.α*(1-P.θ)+P.θ)+P.θ) with hX2
  have hc1 : cDR1 P = P.a / P.b * X1 := by
    rw [hX1]; unfold cDR1 μ; field_simp
  have hc2 : cDR2 P = P.a / P.b * X2 := by
    rw [hX2]; unfold cDR2 μ; field_simp
  have hab : 0 < P.a / P.b := div_pos ha hb
  have hX12 : X1 < X2 := by
    rw [hc1, hc2] at h12; exact lt_of_mul_lt_mul_left h12 hab.le
  have hF2 : F P.α P.θ X2 < 0 := by
    rw [hX2, F_x2 _ _ hα0 hθ0 hθ1]
    apply div_neg_of_neg_of_pos
    · have : 0 < 1 - (P.α*(1-P.θ)+P.θ) := by nlinarith
      have : 0 < P.θ^2*(1-(P.α*(1-P.θ)+P.θ))^2 := by positivity
      linarith
    · have : 0 < (P.α*(1-P.θ)+P.θ)+P.θ := by nlinarith
      positivity
  have hF1 : 0 < F P.α P.θ X1 := by
    have h := interaction_mid_cDR1_pos P hP hα
    have e := yp3_mid P.a P.b P.α P.θ (cDR1 P) ha hb hα0 hθ0 hθ1
    have hμd : μ P = P.α * (1 - P.θ) + P.θ := rfl
    rw [hμd, e] at h
    have hx : P.b * cDR1 P / P.a = X1 := by rw [hc1]; field_simp
    rw [hx] at h
    exact (mul_pos_iff_of_pos_left (by positivity)).mp h
  obtain ⟨r, hr1, hr2, hpos, hneg⟩ :=
    sign_pattern P.α P.θ X1 X2 hα hα1 hθ0 hθ1 hX12 hF1 hF2
  have hX1pos : 0 < X1 := by
    rw [hX1]
    apply div_pos _ hD
    apply mul_pos (by positivity)
    set z := P.α*(P.α*(1-P.θ)+P.θ)*(1-P.α)*(1-P.θ) with hz
    have hz0 : 0 ≤ z := by
      have : 0 < 1 - P.α := by linarith
      positivity
    have ht := Real.sq_sqrt hz0
    have htn := Real.sqrt_nonneg z
    set w := P.α*(1-P.θ)*(1-P.α) with hw
    have hzw : z = (P.α*(1-P.θ)+P.θ) * w := by rw [hz, hw]; ring
    have h2t : 2 * Real.sqrt z ≤ (P.α*(1-P.θ)+P.θ) + w := by
      have hw0 : 0 ≤ w := by
        have : 0 < 1 - P.α := by linarith
        positivity
      nlinarith [sq_nonneg ((P.α*(1-P.θ)+P.θ) - w), sq_nonneg (2 * Real.sqrt z - ((P.α*(1-P.θ)+P.θ) + w))]
    have : 0 < 1 - (P.α*(1-P.θ)+P.θ) - w := by
      rw [hw]
      have : 1 - (P.α*(1-P.θ)+P.θ) - P.α*(1-P.θ)*(1-P.α) = (1-P.α)^2*(1-P.θ) := by ring
      rw [this]
      have : 0 < 1 - P.α := by linarith
      positivity
    nlinarith [mul_le_mul_of_nonneg_left h2t hθ0.le, mul_pos hθ0 this, sq_nonneg (P.α*(1-P.θ)+P.θ)]
  have hX2μ : X2 < μ P := by
    rw [hX2, div_lt_iff₀ (by nlinarith)]; unfold μ; nlinarith
  refine ⟨fun c hc hcμ => ⟨(hL1 c hc hcμ).1, (hL2 c hc hcμ).1, (hL3 c hc hcμ).1, (hL4 c hc hcμ).1⟩,
    P.a / P.b * r, mul_pos hab (by linarith), ?_, ?_⟩
  · calc P.a / P.b * r < P.a / P.b * μ P := by
          apply mul_lt_mul_of_pos_left _ hab; linarith
      _ = P.a * μ P / P.b := by ring
  intro c σOA σOR σDA σDR hc hcμ hOA hOR hDA hDR
  have hbc : P.b * c < P.a * μ P := by rw [lt_div_iff₀ hb] at hcμ; linarith
  have vOA : piR P c .OA σOA = (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * μ P) :=
    (((hL1 c hc hcμ).2 σOA hOA).2.2 (by rw [max_eq_left hOA2]; exact hc)).1
  have vOR : piR P c .OR σOR = (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) :=
    (((hL2 c hc hcμ).2 σOR hOR).2 (by rw [max_eq_left hORn.le]; exact hc)).1
  have hOAOR : (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * μ P)
      < (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
    apply div_lt_div_of_pos_left (by nlinarith) (by positivity)
    nlinarith
  -- conversions between c and the normalized variable
  have hconv : ∀ y : ℝ, (c < P.a / P.b * y ↔ P.b * c / P.a < y) ∧ (P.a / P.b * y < c ↔ y < P.b * c / P.a) := by
    intro y
    constructor
    · rw [div_lt_iff₀ ha, div_mul_eq_mul_div, lt_div_iff₀ hb]; constructor <;> intro h <;> linarith
    · rw [lt_div_iff₀ ha, div_mul_eq_mul_div, div_lt_iff₀ hb]; constructor <;> intro h <;> linarith
  have hmidV : ∀ (hlo : cDR1 P < c) (hhi : c < cDR2 P),
      interaction P c σOA σOR σDA σDR = P.a ^ 2 / P.b * F P.α P.θ (P.b * c / P.a) := by
    intro hlo hhi
    have vDA := (((hL3 c hc hcμ).2 σDA hDA).1 (by linarith)).1
    have vDR := (((hL4 c hc hcμ).2 σDR hDR).2.1 hlo hhi).1
    unfold interaction
    rw [vOA, vOR, vDA, vDR, ← yp3_mid P.a P.b P.α P.θ c ha hb hα0 hθ0 hθ1]
    unfold μ; ring
  have hthird : ∀ (hhi : cDR2 P ≤ c),
      piR P c .DR σDR = (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
    intro hhi
    rcases hhi.lt_or_eq with h | h
    · exact (((hL4 c hc hcμ).2 σDR hDR).2.2 h).1
    · subst h; exact (hL4' σDR hDR).1
  refine ⟨?_, ?_, ?_⟩
  · rintro (h | ⟨h1, h2⟩)
    · have vDA := (((hL3 c hc hcμ).2 σDA hDA).1 (by linarith)).1
      have vDR := (((hL4 c hc hcμ).2 σDR hDR).1 h).1
      unfold interaction
      rw [vOA, vOR, vDA, vDR]
      linarith
    · have vDA := (((hL3 c hc hcμ).2 σDA hDA).1 h2).1
      have hA := yp3_AOA P hP c hc h2 hbc
      rcases lt_or_ge c (cDR2 P) with h3 | h3
      · have hlo : cDR1 P < c := by
          rw [hc1]; exact (hconv X1).2.mpr (by linarith [(hconv r).2.mp h1])
        rw [hmidV hlo h3]
        have hx1 := (hconv r).2.mp h1
        have hx2 : P.b * c / P.a < X2 := (hconv X2).1.mp (by rw [← hc2]; exact h3)
        have := hneg _ hx1 hx2
        have : 0 < P.a ^ 2 / P.b := by positivity
        nlinarith
      · unfold interaction
        rw [vOA, vOR, vDA, hthird h3]
        linarith
  · intro hlo hhi
    have hhi2 : c < cDR2 P := by
      rw [hc2]; have := (hconv r).1.mp hhi; exact (hconv X2).1.mpr (by linarith)
    rw [hmidV hlo hhi2]
    have hx1 : X1 < P.b * c / P.a := (hconv X1).2.mp (by rw [← hc1]; exact hlo)
    have hx2 := (hconv r).1.mp hhi
    have := hpos _ hx1 hx2
    positivity
  · intro h
    have vDA := (((hL3 c hc hcμ).2 σDA hDA).2 h).1
    unfold interaction
    rw [vOA, vOR, vDA, hthird (by linarith)]
    ring
