-- Prove2me | solution 1 for TokenSignal.Asymmetry.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T14:52:25.269873+00:00
-- url     : https://prove2.me/submissions/3c6a7a4e-f75c-4652-be54-02c3e3f4b3c6

import Mathlib
import Definitions.Def_TokenSignal_Asymmetry_Model

set_option autoImplicit false

namespace TokenSignal.Asymmetry

open MeasureTheory ProbabilityTheory

lemma p6_rev (P : Params) (i : Ty) :
    revLaw P i = gaussianReal (P.μ i) (⟨P.σ ^ 2, sq_nonneg _⟩ : NNReal) := rfl

lemma p6_ER (P : Params) (j : Ty) : ER P j = P.μ j / 4 := by
  obtain ⟨v, -, hv⟩ : ∃ v : NNReal, (v : ℝ) = P.σ ^ 2 ∧ revLaw P j = gaussianReal (P.μ j) v :=
    ⟨⟨P.σ ^ 2, sq_nonneg _⟩, rfl, rfl⟩
  unfold ER
  rw [hv, integral_div, integral_id_gaussianReal]

lemma p6_U (P : Params) (i j : Ty) (α : ℝ) :
    U P i j α = cara P.γ (V P i j α - P.C - P.I) := by
  obtain ⟨v, hvσ, hv⟩ : ∃ v : NNReal, (v : ℝ) = P.σ ^ 2 ∧ revLaw P i = gaussianReal (P.μ i) v :=
    ⟨⟨P.σ ^ 2, sq_nonneg _⟩, rfl, rfl⟩
  set s : ℝ := -(P.γ * ((1 - α) / 4)) with hs
  have hint := integrable_exp_mul_gaussianReal (μ := P.μ i) (v := v) s
  have hmgf := congrFun (mgf_id_gaussianReal (μ := P.μ i) (v := v)) s
  rw [mgf] at hmgf
  simp only [id] at hmgf
  unfold U cara
  set A : ℝ := α * ER P j - P.C - P.I with hA
  have hpt : ∀ x : ℝ, P.γ⁻¹ - P.γ⁻¹ * Real.exp (-(P.γ * (α * ER P j + (1 - α) * (x / 4)
      - P.C - P.I))) = P.γ⁻¹ - (P.γ⁻¹ * Real.exp (-(P.γ * A))) * Real.exp (s * x) := by
    intro x
    rw [mul_assoc, ← Real.exp_add]
    congr 3
    rw [hA, hs]; ring
  rw [hv]
  simp_rw [hpt]
  rw [integral_sub (integrable_const _) (hint.const_mul _), integral_const, integral_const_mul,
    hmgf]
  simp only [probReal_univ, one_smul, hvσ]
  rw [mul_assoc, ← Real.exp_add]
  congr 3
  rw [hA, hs, p6_ER]
  unfold V
  ring

lemma p6_cara_le {γ a b : ℝ} (hγ : 0 < γ) : cara γ a ≤ cara γ b ↔ a ≤ b := by
  unfold cara
  have hg : 0 < γ⁻¹ := inv_pos.mpr hγ
  constructor
  · intro h
    have h1 : Real.exp (-(γ * b)) ≤ Real.exp (-(γ * a)) := by
      by_contra hc
      rw [not_le] at hc
      nlinarith [mul_lt_mul_of_pos_left hc hg]
    rw [Real.exp_le_exp] at h1
    nlinarith
  · intro h
    have h1 : Real.exp (-(γ * b)) ≤ Real.exp (-(γ * a)) := Real.exp_le_exp.mpr (by nlinarith)
    nlinarith [mul_le_mul_of_nonneg_left h1 hg.le]

lemma p6_U_le (P : Params) (hγ : 0 < P.γ) (i j i' j' : Ty) (α α' : ℝ) :
    U P i j α ≤ U P i' j' α' ↔ V P i j α ≤ V P i' j' α' := by
  rw [p6_U, p6_U, p6_cara_le hγ]
  constructor <;> intro h <;> linarith

lemma p6_se_imp (P : Params) (m : Method) (hγ : 0 < P.γ) (hΔ : P.μL < P.μH) :
    (∃ t, IsSE P m t) →
      αbar P m .H < 1 ∧
        8 * αbar P m .H * (P.μH - P.μL) ≤ P.γ * (1 - αbar P m .H) ^ 2 * P.σ ^ 2 := by
  rintro ⟨t, hHt, ht1, _, ⟨α, hαL, hα⟩⟩
  have h := hα t ⟨hHt, le_rfl⟩
  rw [p6_U_le P hγ] at h
  obtain ⟨_, htα, hα1⟩ := hαL
  unfold V Params.μ at h
  set a := αbar P m .H
  have hk : 0 ≤ P.γ * P.σ ^ 2 := by positivity
  have hsq : 0 ≤ P.γ * (1 - α) ^ 2 * P.σ ^ 2 := by positivity
  have hg : 8 * t * (P.μH - P.μL) ≤ P.γ * (1 - t) ^ 2 * P.σ ^ 2 := by nlinarith
  refine ⟨by linarith, ?_⟩
  have h1 : 8 * a * (P.μH - P.μL) ≤ 8 * t * (P.μH - P.μL) := by nlinarith
  have h2 : (1 - t) ^ 2 ≤ (1 - a) ^ 2 := by nlinarith
  have h3 : P.γ * P.σ ^ 2 * (1 - t) ^ 2 ≤ P.γ * P.σ ^ 2 * (1 - a) ^ 2 :=
    mul_le_mul_of_nonneg_left h2 hk
  nlinarith

lemma p6_se_of (P : Params) (m : Method) (hγ : 0 < P.γ) (hΔ : P.μL < P.μH)
    (hL1 : αbar P m .L ≤ 1) (ha1 : αbar P m .H < 1)
    (hc : 8 * αbar P m .H * (P.μH - P.μL) ≤ P.γ * (1 - αbar P m .H) ^ 2 * P.σ ^ 2) :
    ∃ t, IsSE P m t := by
  set a := αbar P m .H with ha
  set g : ℝ → ℝ := fun t => P.γ * (1 - t) ^ 2 * P.σ ^ 2 - 8 * t * (P.μH - P.μL) with hgdef
  have hcont : ContinuousOn g (Set.Icc a 1) := by
    rw [hgdef]; fun_prop
  have hmem : (0 : ℝ) ∈ Set.Icc (g 1) (g a) := by
    simp only [hgdef, Set.mem_Icc]
    constructor <;> nlinarith
  obtain ⟨t0, ⟨hat0, ht01⟩, hg0⟩ := intermediate_value_Icc' ha1.le hcont hmem
  simp only [hgdef] at hg0
  have ht0 : t0 < 1 := by
    rcases lt_or_eq_of_le ht01 with h | h
    · exact h
    · subst h; nlinarith
  have hk : 0 ≤ P.γ * P.σ ^ 2 := by positivity
  refine ⟨t0, hat0, ht0, ?_, ?_⟩
  · intro α hα
    obtain ⟨_, htα, hα1⟩ := hα
    refine ⟨t0, ⟨hat0, le_rfl⟩, ?_⟩
    rw [p6_U_le P hγ]
    unfold V Params.μ
    have hsq : 0 ≤ P.γ * (1 - α) ^ 2 * P.σ ^ 2 := by positivity
    nlinarith
  · refine ⟨1, ⟨hL1, ht0, le_rfl⟩, ?_⟩
    intro α' hα'
    obtain ⟨h1, h2⟩ := hα'
    rw [p6_U_le P hγ]
    unfold V Params.μ
    have h3 : (1 - t0) ^ 2 ≤ (1 - α') ^ 2 := by nlinarith
    have h4 : P.γ * P.σ ^ 2 * (1 - t0) ^ 2 ≤ P.γ * P.σ ^ 2 * (1 - α') ^ 2 :=
      mul_le_mul_of_nonneg_left h3 hk
    nlinarith

lemma p6_SA_iff (Q : Params) (hγ : 0 < Q.γ) (hΔ : Q.μL < Q.μH) (hI : 0 < Q.I)
    (hC : 0 < Q.C) (hL : 4 * (Q.I + Q.C) ≤ Q.μL) :
    SignalingAdvantage Q ↔
      (8 * (Q.I / (Q.μH / 4)) * (Q.μH - Q.μL) ≤
          Q.γ * (1 - Q.I / (Q.μH / 4)) ^ 2 * Q.σ ^ 2 ∧
        Q.γ * (1 - Q.I / (Q.μH / 4 - Q.C)) ^ 2 * Q.σ ^ 2 <
          8 * (Q.I / (Q.μH / 4 - Q.C)) * (Q.μH - Q.μL)) := by
  have htH : αbar Q .token .H = Q.I / (Q.μH / 4) := by
    simp only [αbar, p6_ER, Params.μ]
  have heH : αbar Q .equity .H = Q.I / (Q.μH / 4 - Q.C) := by
    simp only [αbar, p6_ER, Params.μ]
  have htL : αbar Q .token .L ≤ 1 := by
    simp only [αbar, p6_ER, Params.μ]
    rw [div_le_one (by linarith)]; linarith
  have heL : αbar Q .equity .L ≤ 1 := by
    simp only [αbar, p6_ER, Params.μ]
    rw [div_le_one (by linarith)]; linarith
  have ht1 : Q.I / (Q.μH / 4) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have he1 : Q.I / (Q.μH / 4 - Q.C) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  unfold SignalingAdvantage
  constructor
  · rintro ⟨htok, hne⟩
    have h1 := (p6_se_imp Q .token hγ hΔ htok).2
    rw [htH] at h1
    refine ⟨h1, ?_⟩
    by_contra hcon
    rw [not_lt] at hcon
    apply hne
    exact p6_se_of Q .equity hγ hΔ heL (by rw [heH]; exact he1) (by rw [heH]; exact hcon)
  · rintro ⟨h1, h2⟩
    refine ⟨p6_se_of Q .token hγ hΔ htL (by rw [htH]; exact ht1) (by rw [htH]; exact h1), ?_⟩
    intro hex
    have h3 := (p6_se_imp Q .equity hγ hΔ hex).2
    rw [heH] at h3
    linarith

end TokenSignal.Asymmetry

open TokenSignal.Asymmetry in
theorem solution (P : Params) (hS : P.Standing) :
    (∃ μl μu : ℝ, μl < μu ∧ ∀ μL' : ℝ,
      4 * (P.I + P.C) ≤ μL' → μL' < P.μH →
        (SignalingAdvantage { P with μL := μL' } ↔ μl ≤ μL' ∧ μL' < μu)) ∧
    (∃ σl σu : ℝ, σl < σu ∧ ∀ σ' : ℝ, 0 < σ' →
        (SignalingAdvantage { P with σ := σ' } ↔ σl ≤ σ' ∧ σ' < σu)) := by
  obtain ⟨hγ, hσ, hΔ, hC, hI, hfeas⟩ := hS
  set a1 := P.I / (P.μH / 4) with ha1
  set a2 := P.I / (P.μH / 4 - P.C) with ha2
  have hb : 0 < P.μH / 4 - P.C := by linarith
  have ha1p : 0 < a1 := by rw [ha1]; exact div_pos hI (by linarith)
  have ha12 : a1 < a2 := by
    rw [ha1, ha2]; exact div_lt_div_of_pos_left hI hb (by linarith)
  have ha21 : a2 < 1 := by
    rw [ha2, div_lt_one hb]; linarith
  have ha2p : 0 < a2 := by linarith
  have hk : 0 < P.γ * P.σ ^ 2 := by positivity
  have hq : a1 * (1 - a2) ^ 2 < a2 * (1 - a1) ^ 2 := by
    have e1 : (1 - a2) ^ 2 < (1 - a1) ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left e1 ha1p]
  refine ⟨⟨P.μH - P.γ * (1 - a1) ^ 2 * P.σ ^ 2 / (8 * a1),
      P.μH - P.γ * (1 - a2) ^ 2 * P.σ ^ 2 / (8 * a2), ?_, ?_⟩,
    ⟨Real.sqrt (8 * a1 * (P.μH - P.μL) / (P.γ * (1 - a1) ^ 2)),
      Real.sqrt (8 * a2 * (P.μH - P.μL) / (P.γ * (1 - a2) ^ 2)), ?_, ?_⟩⟩
  · have : P.γ * (1 - a2) ^ 2 * P.σ ^ 2 / (8 * a2) < P.γ * (1 - a1) ^ 2 * P.σ ^ 2 / (8 * a1) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_lt_mul_of_pos_left hq hk]
    linarith
  · intro μL' hL' hlt
    rw [p6_SA_iff { P with μL := μL' } hγ hlt hI hC hL']
    dsimp only
    rw [← ha1, ← ha2]
    have e1 : 8 * a1 * (P.μH - μL') ≤ P.γ * (1 - a1) ^ 2 * P.σ ^ 2 ↔
        P.μH - P.γ * (1 - a1) ^ 2 * P.σ ^ 2 / (8 * a1) ≤ μL' := by
      rw [sub_le_comm, le_div_iff₀ (by positivity)]
      constructor <;> intro h <;> linarith
    have e2 : P.γ * (1 - a2) ^ 2 * P.σ ^ 2 < 8 * a2 * (P.μH - μL') ↔
        μL' < P.μH - P.γ * (1 - a2) ^ 2 * P.σ ^ 2 / (8 * a2) := by
      rw [lt_sub_comm, div_lt_iff₀ (by positivity)]
      constructor <;> intro h <;> linarith
    rw [e1, e2]
  · have hΔp : 0 < P.μH - P.μL := by linarith
    have hd1 : 0 < P.γ * (1 - a1) ^ 2 := by
      have : 0 < 1 - a1 := by linarith
      positivity
    have hd2 : 0 < P.γ * (1 - a2) ^ 2 := by
      have : 0 < 1 - a2 := by linarith
      positivity
    apply Real.sqrt_lt_sqrt (div_nonneg (by nlinarith) hd1.le)
    rw [div_lt_div_iff₀ hd1 hd2]
    have := mul_lt_mul_of_pos_left hq (mul_pos (mul_pos (by norm_num : (0:ℝ) < 8) hΔp) hγ)
    nlinarith
  · intro σ' hσ'
    have hfe : 4 * (P.I + P.C) ≤ P.μL := by linarith
    rw [p6_SA_iff { P with σ := σ' } hγ hΔ hI hC hfe]
    dsimp only
    rw [← ha1, ← ha2]
    have hd1 : 0 < P.γ * (1 - a1) ^ 2 := by
      have : 0 < 1 - a1 := by linarith
      positivity
    have hd2 : 0 < P.γ * (1 - a2) ^ 2 := by
      have : 0 < 1 - a2 := by linarith
      positivity
    have e1 : 8 * a1 * (P.μH - P.μL) ≤ P.γ * (1 - a1) ^ 2 * σ' ^ 2 ↔
        Real.sqrt (8 * a1 * (P.μH - P.μL) / (P.γ * (1 - a1) ^ 2)) ≤ σ' := by
      rw [Real.sqrt_le_left hσ'.le, div_le_iff₀ hd1]
      constructor <;> intro h <;> linarith
    have e2 : P.γ * (1 - a2) ^ 2 * σ' ^ 2 < 8 * a2 * (P.μH - P.μL) ↔
        σ' < Real.sqrt (8 * a2 * (P.μH - P.μL) / (P.γ * (1 - a2) ^ 2)) := by
      rw [Real.lt_sqrt hσ'.le, lt_div_iff₀ hd2]
      constructor <;> intro h <;> linarith
    rw [e1, e2]
