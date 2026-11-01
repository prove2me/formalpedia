-- Prove2me | solution 1 for PandemicInfo.Inequality.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:13:21.30237+00:00
-- url     : https://prove2.me/submissions/60151be0-8016-42f4-a45f-044cb49acf94

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_PandemicInfo_Inequality_Model
import Definitions.Def_PandemicInfo_Inequality_Reduced

namespace PandemicThm2Aux
open PandemicInfo.Inequality

lemma kg_lt (P : Params) (σ' : ℝ) (hσ : P.σ < σ') (hS : P.Standing) :
    ({ P with σ := σ' } : Params).κ / ({ P with σ := σ' } : Params).γ < P.κ / P.γ := by
  obtain ⟨_, _, _, _, _, hσ0, _, hκ, _⟩ := hS
  show P.κ / (σ' * 2 * Real.sqrt 3) < P.κ / (P.σ * 2 * Real.sqrt 3)
  have h3 : 0 < Real.sqrt 3 := by positivity
  apply div_lt_div_of_pos_left hκ (by positivity)
  nlinarith

lemma part1 (P : Params) (σ' : ℝ) (hσ : P.σ < σ') (hS : P.Standing) :
    (({ P with σ := σ' } : Params).lam1 ≤ P.lam1 ∧ ({ P with σ := σ' } : Params).lam2 ≤ P.lam2 ∧
      ({ P with σ := σ' } : Params).lam3 ≤ P.lam3 ∧ ({ P with σ := σ' } : Params).lam4 ≤ P.lam4) := by
  have hk := (kg_lt P σ' hσ hS).le
  set r' := ({ P with σ := σ' } : Params).κ / ({ P with σ := σ' } : Params).γ
  set r := P.κ / P.γ
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply csSup_le_csSup
    · refine ⟨1/2, ?_⟩
      rintro x (rfl | ⟨⟨_, hx⟩, _⟩) <;> linarith
    · exact Set.insert_nonempty _ _
    · apply Set.insert_subset_insert
      rintro x ⟨hx, hx2⟩
      exact ⟨hx, le_trans (show P.Gl x ≤ r' from hx2) hk⟩
  · apply csSup_le_csSup
    · refine ⟨1/2, ?_⟩
      rintro x (rfl | ⟨⟨_, hx⟩, _⟩) <;> linarith
    · exact Set.insert_nonempty _ _
    · apply Set.insert_subset_insert
      rintro x ⟨hx, hx2⟩
      exact ⟨hx, le_trans (show P.G2 x ≤ r' from hx2) hk⟩
  · apply csInf_le_csInf
    · refine ⟨0, ?_⟩
      rintro x (rfl | ⟨⟨hx, _⟩, _⟩) <;> linarith
    · exact Set.insert_nonempty _ _
    · apply Set.insert_subset_insert
      rintro x ⟨hx, hx2⟩
      exact ⟨hx, le_trans hk (show r ≤ P.G1 x from hx2)⟩
  · apply csInf_le_csInf
    · refine ⟨0, ?_⟩
      rintro x (rfl | ⟨⟨hx, _⟩, _⟩) <;> linarith
    · exact Set.insert_nonempty _ _
    · apply Set.insert_subset_insert
      rintro x ⟨hx, hx2⟩
      exact ⟨hx, le_trans hk (show r ≤ P.Gh x from hx2)⟩

example (pl ph : ℝ) : binPolicy pl ph 0 0 = pl ∧ binPolicy pl ph 0 1 = 1 - pl ∧
    binPolicy pl ph 1 0 = 1 - ph ∧ binPolicy pl ph 1 1 = ph := by
  simp [binPolicy]


lemma int_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (h : ∀ x ∈ Set.Ioo a b, f x = g x) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo h

lemma std_facts (P : Params) (hS : P.Standing) :
    0 < P.γ ∧ P.γ = P.cHi - P.cLo ∧ 0 < P.cHi ∧ P.cLo < P.cHi := by
  obtain ⟨_, _, _, _, _, hσ0, hθ, hκ, _⟩ := hS
  have h3 : 0 < Real.sqrt 3 := by positivity
  unfold Params.γ Params.cHi Params.cLo
  refine ⟨by positivity, by ring, by nlinarith, by nlinarith⟩

lemma bne_char (P : Params) (hS : P.Standing) (a : ℝ → ℝ → ℝ) (μ : ℝ)
    (hμ : μ ∈ Set.Icc P.ωl P.ωh) (h : P.IsBNEAt a μ) :
    P.activePop a μ = (P.cHi - P.cStar μ) / P.γ ∧
    P.econCost a μ = (P.cStar μ ^ 2 - P.cLo ^ 2) / (2 * P.γ) ∧
    P.healthCost a μ = P.cStar μ * (P.cHi - P.cStar μ) / P.γ := by
  obtain ⟨hγ, hγe, hhi, hlohi⟩ := std_facts P hS
  obtain ⟨hωl, _, _, _, _, hσ0, hθ, hκ, hlo⟩ := hS
  obtain ⟨hint, hb⟩ := h
  set A := P.activePop a μ with hA
  set T := μ * A * P.κ with hT
  set lo := P.cLo
  set hi := P.cHi
  have h1 : ∀ c ∈ Set.Icc lo hi, c < T → a c μ = 1 := by
    intro c hc hcT
    obtain ⟨ha, hi'⟩ := hb c hc
    rcases ha with ha | ha
    · have := hi' 1 (Or.inr rfl)
      rw [ha] at this
      nlinarith
    · exact ha
  have h0 : ∀ c ∈ Set.Icc lo hi, T < c → a c μ = 0 := by
    intro c hc hcT
    obtain ⟨ha, hi'⟩ := hb c hc
    rcases ha with ha | ha
    · exact ha
    · have := hi' 0 (Or.inl rfl)
      rw [ha] at this
      nlinarith
  have hApop : A = (∫ c in lo..hi, (1 - a c μ)) / P.γ := rfl
  have hint1 : IntervalIntegrable (fun c => 1 - a c μ) MeasureTheory.volume lo hi :=
    intervalIntegrable_const.sub hint
  have hμκ : lo ≤ μ * P.κ := le_trans hlo (by nlinarith [hμ.1])
  -- locate T
  rcases lt_or_ge T lo with hTlo | hTlo
  · exfalso
    have : (∫ c in lo..hi, (1 - a c μ)) = ∫ c in lo..hi, (1 : ℝ) := by
      apply int_congr_Ioo hlohi.le
      intro x hx
      rw [h0 x ⟨hx.1.le, hx.2.le⟩ (by linarith [hx.1])]; ring
    rw [this, intervalIntegral.integral_const, hγe] at hApop
    have hA1 : A = 1 := by rw [hApop]; field_simp [(sub_pos.2 hlohi).ne']; simp
    rw [hA1] at hT
    linarith
  rcases lt_or_ge hi T with hThi | hThi
  · exfalso
    have : (∫ c in lo..hi, (1 - a c μ)) = ∫ c in lo..hi, (0 : ℝ) := by
      apply int_congr_Ioo hlohi.le
      intro x hx
      rw [h1 x ⟨hx.1.le, hx.2.le⟩ (by linarith [hx.2])]; ring
    rw [this, intervalIntegral.integral_zero] at hApop
    have hA0 : A = 0 := by rw [hApop]; simp
    rw [hA0] at hT
    linarith
  -- lo ≤ T ≤ hi
  have hsub1 : Set.uIcc lo T ⊆ Set.uIcc lo hi := Set.uIcc_subset_uIcc_left (Set.mem_uIcc.2 (Or.inl ⟨hTlo, hThi⟩))
  have hsub2 : Set.uIcc T hi ⊆ Set.uIcc lo hi := Set.uIcc_subset_uIcc_right (Set.mem_uIcc.2 (Or.inl ⟨hTlo, hThi⟩))
  have hI1 : (∫ c in lo..hi, (1 - a c μ)) = hi - T := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint1.mono_set hsub1) (hint1.mono_set hsub2)]
    have e1 : (∫ c in lo..T, (1 - a c μ)) = ∫ c in lo..T, (0 : ℝ) := by
      apply int_congr_Ioo hTlo
      intro x hx
      rw [h1 x ⟨hx.1.le, by linarith [hx.2]⟩ hx.2]; ring
    have e2 : (∫ c in T..hi, (1 - a c μ)) = ∫ c in T..hi, (1 : ℝ) := by
      apply int_congr_Ioo hThi
      intro x hx
      rw [h0 x ⟨by linarith [hx.1], hx.2.le⟩ hx.1]; ring
    rw [e1, e2]; simp
  have hAv : A = (hi - T) / P.γ := by rw [hApop, hI1]
  have hTc : T = P.cStar μ := by
    have hγ' : P.γ = P.σ * 2 * Real.sqrt 3 := rfl
    have hhi' : hi = P.θ + P.σ * Real.sqrt 3 := rfl
    have hden : 0 < P.σ * 2 * Real.sqrt 3 + μ * P.κ := by
      have : 0 < μ := lt_of_lt_of_le hωl hμ.1
      rw [← hγ']; positivity
    unfold Params.cStar
    rw [eq_div_iff hden.ne', ← hhi', ← hγ']
    have hAγ : A * P.γ = hi - T := by rw [hAv]; field_simp
    have : T * P.γ = μ * P.κ * (hi - T) := by
      rw [← hAγ, hT]; ring
    linarith
  refine ⟨by rw [hAv, hTc], ?_, ?_⟩
  · have hintm : IntervalIntegrable (fun c => a c μ * c) MeasureTheory.volume lo hi :=
      hint.mul_continuousOn continuousOn_id
    unfold Params.econCost Params.Ec
    rw [← intervalIntegral.integral_add_adjacent_intervals (hintm.mono_set hsub1) (hintm.mono_set hsub2)]
    have e1 : (∫ c in lo..T, a c μ * c) = ∫ c in lo..T, c := by
      apply int_congr_Ioo hTlo
      intro x hx
      rw [h1 x ⟨hx.1.le, by linarith [hx.2]⟩ hx.2]; ring
    have e2 : (∫ c in T..hi, a c μ * c) = ∫ c in T..hi, (0 : ℝ) := by
      apply int_congr_Ioo hThi
      intro x hx
      rw [h0 x ⟨by linarith [hx.1], hx.2.le⟩ hx.1]; ring
    rw [e1, e2, integral_id, ← hTc]; simp; rw [div_div]
  · unfold Params.healthCost Params.Ec
    have : (fun c => (1 - a c μ) * μ * P.activePop a μ * P.κ) = fun c => (1 - a c μ) * T := by
      funext c; rw [hT]; ring
    rw [this, intervalIntegral.integral_mul_const, hI1, ← hTc]
    field_simp

lemma chord_core (κ g h b lam μ e : ℝ) (hκ : 0 < κ) (hg : 0 < g) (hb : 0 < b)
    (hμ : 0 < μ) (he : 0 < e) (hμb : μ ≠ b) (heb : e ≠ b)
    (heq : e * (κ * (g * lam + 2 * κ * b * (2 * lam - 1))) =
      g * (g * (5 * lam - 4) + 2 * κ * b * (lam - 1))) :
    ((lam * ((μ*κ*h/(g+μ*κ)) ^ 2 - (h - g) ^ 2) / (2 * g) + (1 - lam) * (μ*κ*h/(g+μ*κ)) * (h - (μ*κ*h/(g+μ*κ))) / g
       - (lam * ((b*κ*h/(g+b*κ)) ^ 2 - (h - g) ^ 2) / (2 * g) + (1 - lam) * (b*κ*h/(g+b*κ)) * (h - (b*κ*h/(g+b*κ))) / g)) / (μ - b)
     - (lam * ((e*κ*h/(g+e*κ)) ^ 2 - (h - g) ^ 2) / (2 * g) + (1 - lam) * (e*κ*h/(g+e*κ)) * (h - (e*κ*h/(g+e*κ))) / g
       - (lam * ((b*κ*h/(g+b*κ)) ^ 2 - (h - g) ^ 2) / (2 * g) + (1 - lam) * (b*κ*h/(g+b*κ)) * (h - (b*κ*h/(g+b*κ))) / g)) / (e - b))
      * (2 * g * (g + b * κ)) = κ * (2 - 3 * lam) * ((μ*κ*h/(g+μ*κ)) - (e*κ*h/(g+e*κ))) ^ 2 := by
  have hS : ∀ u : ℝ, 0 < u → u ≠ b →
      (lam * ((u*κ*h/(g+u*κ)) ^ 2 - (h - g) ^ 2) / (2 * g) + (1 - lam) * (u*κ*h/(g+u*κ)) * (h - (u*κ*h/(g+u*κ))) / g
       - (lam * ((b*κ*h/(g+b*κ)) ^ 2 - (h - g) ^ 2) / (2 * g) + (1 - lam) * (b*κ*h/(g+b*κ)) * (h - (b*κ*h/(g+b*κ))) / g)) / (u - b)
      = κ * (h - u*κ*h/(g+u*κ)) * ((3*lam-2)/2 * (u*κ*h/(g+u*κ) + b*κ*h/(g+b*κ)) + (1-lam)*h) / (g * (g + b*κ)) := by
    intro u hu hub
    have h1 : 0 < g + u * κ := by positivity
    have h2 : 0 < g + b * κ := by positivity
    have h3 : u - b ≠ 0 := sub_ne_zero.2 hub
    rw [div_eq_iff h3]
    field_simp
    ring
  rw [hS μ hμ hμb, hS e he heb]
  set y := μ*κ*h/(g+μ*κ)
  set ye := e*κ*h/(g+e*κ)
  set yb := b*κ*h/(g+b*κ)
  have hv : 2 * (2 - 3*lam) * ye = (2 - 3*lam) * (h - yb) + 2 * (1 - lam) * h := by
    have h1 : 0 < g + e * κ := by positivity
    have h2 : 0 < g + b * κ := by positivity
    simp only [ye, yb]
    field_simp
    linear_combination (-h) * heq
  have h2 : 0 < g + b * κ := by positivity
  field_simp
  clear_value y ye yb
  linear_combination (y - ye) * hv


lemma cStar_mem (P : Params) (hS : P.Standing) (μ : ℝ) (hμ : μ ∈ Set.Icc P.ωl P.ωh) :
    P.cLo ≤ P.cStar μ ∧ P.cStar μ ≤ P.cHi := by
  obtain ⟨hγ, hγe, hhi, hlohi⟩ := std_facts P hS
  obtain ⟨hωl, _, _, _, _, hσ0, hθ, hκ, hlo⟩ := hS
  have hμ0 : 0 < μ := lt_of_lt_of_le hωl hμ.1
  have hc : P.cStar μ = μ * P.κ * P.cHi / (P.γ + μ * P.κ) := rfl
  have hden : 0 < P.γ + μ * P.κ := by positivity
  have hμκ : P.cLo ≤ μ * P.κ := le_trans hlo (by nlinarith [hμ.1])
  rw [hc]
  constructor
  · rw [le_div_iff₀ hden]; nlinarith
  · rw [div_le_iff₀ hden]; nlinarith [mul_pos hhi hγ]

lemma a0_bne (P : Params) (hS : P.Standing) :
    P.IsBNEProfile (fun c μ => if c ≤ P.cStar μ then (1 : ℝ) else 0) := by
  intro μ hμ
  obtain ⟨hγ, hγe, hhi, hlohi⟩ := std_facts P hS
  obtain ⟨hlo', hhi'⟩ := cStar_mem P hS μ hμ
  have hωl := hS.1
  have hκ := hS.2.2.2.2.2.2.2.1
  have hμ0 : 0 < μ := lt_of_lt_of_le hωl hμ.1
  set s := P.cStar μ with hs
  have hanti : Antitone (fun c : ℝ => if c ≤ s then (1 : ℝ) else 0) := by
    intro x y hxy
    by_cases hy : y ≤ s
    · have : x ≤ s := le_trans hxy hy
      simp [hy, this]
    · simp only [hy, if_false]; split_ifs <;> norm_num
  have hmono : Monotone (fun c : ℝ => 1 - (if c ≤ s then (1 : ℝ) else 0)) := by
    intro x y hxy; have := hanti hxy; simp only at this ⊢; linarith
  have hA : P.activePop (fun c μ => if c ≤ P.cStar μ then (1 : ℝ) else 0) μ = (P.cHi - s) / P.γ := by
    unfold Params.activePop Params.Ec
    congr 1
    show (∫ c in P.cLo..P.cHi, (1 - if c ≤ s then (1 : ℝ) else 0)) = P.cHi - s
    rw [← intervalIntegral.integral_add_adjacent_intervals (hmono.intervalIntegrable)
      (hmono.intervalIntegrable) (b := s)]
    have e1 : (∫ c in P.cLo..s, (1 - if c ≤ s then (1 : ℝ) else 0)) = ∫ c in P.cLo..s, (0 : ℝ) := by
      apply int_congr_Ioo hlo'
      intro x hx; simp [hx.2.le]
    have e2 : (∫ c in s..P.cHi, (1 - if c ≤ s then (1 : ℝ) else 0)) = ∫ c in s..P.cHi, (1 : ℝ) := by
      apply int_congr_Ioo hhi'
      intro x hx; simp [not_le.2 hx.1]
    rw [e1, e2]; simp
  have hT : μ * ((P.cHi - s) / P.γ) * P.κ = s := by
    have hc : s = μ * P.κ * P.cHi / (P.γ + μ * P.κ) := rfl
    have hden : 0 < P.γ + μ * P.κ := by positivity
    rw [hc]; field_simp; ring
  refine ⟨hanti.intervalIntegrable, ?_⟩
  intro c hc
  rw [hA]
  have hT' : ∀ α : ℝ, (1 - α) * μ * ((P.cHi - s) / P.γ) * P.κ = (1 - α) * s := by
    intro α
    calc (1 - α) * μ * ((P.cHi - s) / P.γ) * P.κ = (1 - α) * (μ * ((P.cHi - s) / P.γ) * P.κ) := by ring
      _ = (1 - α) * s := by rw [hT]
  by_cases hcs : c ≤ s
  · beta_reduce; rw [if_pos (show c ≤ P.cStar μ from hcs)]
    refine ⟨Or.inr rfl, ?_⟩
    intro α hα
    rw [hT', hT']
    rcases hα with rfl | rfl <;> nlinarith
  · beta_reduce; rw [if_neg (show ¬ c ≤ P.cStar μ from hcs)]
    refine ⟨Or.inl rfl, ?_⟩
    intro α hα
    rw [hT', hT']
    push Not at hcs
    rcases hα with rfl | rfl <;> nlinarith

/-- reduced cost at a posterior mean -/
noncomputable def Φ (P : Params) (lam μ : ℝ) : ℝ :=
  lam * (P.cStar μ ^ 2 - P.cLo ^ 2) / (2 * P.γ) + (1 - lam) * P.cStar μ * (P.cHi - P.cStar μ) / P.γ

lemma postMean_mem (P : Params) (hS : P.Standing) {M : Type} [Fintype M] (π : Fin 2 → M → ℝ)
    (hπ : IsPolicy π) (m : M) : P.postMean π m ∈ Set.Icc P.ωl P.ωh := by
  obtain ⟨hωl, hlh, _, hρ0, hρ1, _⟩ := hS
  have h1 := hπ.1 1 m
  have h0 := hπ.1 0 m
  have hx : 0 ≤ π 1 m * P.ρ0 := by positivity
  have hy : 0 ≤ π 0 m * (1 - P.ρ0) := mul_nonneg h0 (by linarith)
  have hp0 : 0 ≤ P.postHigh π m := div_nonneg hx (by linarith)
  have hp1 : P.postHigh π m ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
  unfold Params.postMean
  constructor <;> nlinarith

lemma gov_eq (P : Params) (hS : P.Standing) (lam : ℝ) {M : Type} [Fintype M] (π : Fin 2 → M → ℝ)
    (hπ : IsPolicy π) (a : ℝ → ℝ → ℝ) (ha : P.IsBNEProfile a) :
    P.govCost lam π a = ∑ m, P.msgProb π m * Φ P lam (P.postMean π m) := by
  unfold Params.govCost
  refine Finset.sum_congr rfl (fun m _ => ?_)
  obtain ⟨_, he, hh⟩ := bne_char P hS a _ (postMean_mem P hS π hπ m) (ha _ (postMean_mem P hS π hπ m))
  rw [he, hh]; unfold Φ; ring

lemma binPolicy_isPolicy (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    IsPolicy (binPolicy x y) := by
  refine ⟨?_, ?_⟩
  · intro ω m
    fin_cases ω <;> fin_cases m <;> simp [binPolicy] <;> linarith
  · intro ω
    fin_cases ω <;> simp [binPolicy, Fin.sum_univ_two]

lemma mh_eq (P : Params) (hS : P.Standing) (x : ℝ) (hx1 : x ≤ 1) :
    P.postMean (binPolicy x 1) 1 = P.ωl + P.ρ0 * (P.ωh - P.ωl) / (P.ρ0 + (1 - P.ρ0) * (1 - x)) := by
  obtain ⟨hωl, hlh, _, hρ0, hρ1, _⟩ := hS
  have hq : 0 < P.ρ0 + (1 - P.ρ0) * (1 - x) := by nlinarith
  unfold Params.postMean Params.postHigh
  simp [binPolicy]
  rw [show P.ρ0 + (1 - x) * (1 - P.ρ0) = P.ρ0 + (1 - P.ρ0) * (1 - x) by ring]
  field_simp; ring

lemma ex_cost (P : Params) (hS : P.Standing) (lam x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (a : ℝ → ℝ → ℝ) (ha : P.IsBNEProfile a) :
    P.govCost lam (binPolicy x 1) a = Φ P lam P.ωl + P.ρ0 * (P.ωh - P.ωl) *
      ((Φ P lam (P.postMean (binPolicy x 1) 1) - Φ P lam P.ωl) / (P.postMean (binPolicy x 1) 1 - P.ωl)) := by
  rw [gov_eq P hS lam _ (binPolicy_isPolicy x 1 hx0 hx1 zero_le_one le_rfl) a ha, Fin.sum_univ_two,
    mh_eq P hS x hx1]
  obtain ⟨hωl, hlh, _, hρ0, hρ1, _⟩ := hS
  have hq : 0 < P.ρ0 + (1 - P.ρ0) * (1 - x) := by nlinarith
  have hm0 : P.postMean (binPolicy x 1) 0 = P.ωl := by
    unfold Params.postMean Params.postHigh; simp [binPolicy]
  rw [hm0]
  have hd : 0 < P.ρ0 * (P.ωh - P.ωl) := mul_pos hρ0 (by linarith)
  have p0 : P.msgProb (binPolicy x 1) 0 = (1 - P.ρ0) * x := by
    unfold Params.msgProb; simp [binPolicy]
  have p1 : P.msgProb (binPolicy x 1) 1 = P.ρ0 + (1 - P.ρ0) * (1 - x) := by
    unfold Params.msgProb; simp [binPolicy]
  rw [p0, p1]
  set q := P.ρ0 + (1 - P.ρ0) * (1 - x)
  have hm : P.ωl + P.ρ0 * (P.ωh - P.ωl) / q - P.ωl = P.ρ0 * (P.ωh - P.ωl) / q := by ring
  rw [hm]
  generalize Φ P lam (P.ωl + P.ρ0 * (P.ωh - P.ωl) / q) = F
  generalize Φ P lam P.ωl = Fl
  have hne : P.ωh - P.ωl ≠ 0 := (sub_pos.2 hlh).ne'
  field_simp
  simp only [q]; ring


lemma ml_eq (P : Params) (hS : P.Standing) (x : ℝ) (hx1 : x ≤ 1) :
    P.postMean (binPolicy 1 x) 0 =
      P.ωl + (1 - x) * P.ρ0 * (P.ωh - P.ωl) / ((1 - x) * P.ρ0 + (1 - P.ρ0)) := by
  obtain ⟨hωl, hlh, _, hρ0, hρ1, _⟩ := hS
  have hq : 0 < (1 - x) * P.ρ0 + (1 - P.ρ0) := by nlinarith
  unfold Params.postMean Params.postHigh
  simp [binPolicy]
  field_simp; ring

lemma dp_cost (P : Params) (hS : P.Standing) (lam x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (a : ℝ → ℝ → ℝ) (ha : P.IsBNEProfile a) :
    P.govCost lam (binPolicy 1 x) a = Φ P lam P.ωh - (1 - P.ρ0) * (P.ωh - P.ωl) *
      ((Φ P lam (P.postMean (binPolicy 1 x) 0) - Φ P lam P.ωh) / (P.postMean (binPolicy 1 x) 0 - P.ωh)) := by
  rw [gov_eq P hS lam _ (binPolicy_isPolicy 1 x zero_le_one le_rfl hx0 hx1) a ha, Fin.sum_univ_two,
    ml_eq P hS x hx1]
  obtain ⟨hωl, hlh, _, hρ0, hρ1, _⟩ := hS
  have hq : 0 < (1 - x) * P.ρ0 + (1 - P.ρ0) := by nlinarith
  have p0 : P.msgProb (binPolicy 1 x) 0 = (1 - x) * P.ρ0 + (1 - P.ρ0) := by
    unfold Params.msgProb; simp [binPolicy]; ring
  have p1 : P.msgProb (binPolicy 1 x) 1 = P.ρ0 * x := by
    unfold Params.msgProb; simp [binPolicy]
  have t1 : P.msgProb (binPolicy 1 x) 1 * Φ P lam (P.postMean (binPolicy 1 x) 1) = P.ρ0 * x * Φ P lam P.ωh := by
    rw [p1]
    rcases eq_or_lt_of_le hx0 with hx | hx
    · rw [← hx]; simp
    · have : P.postMean (binPolicy 1 x) 1 = P.ωh := by
        unfold Params.postMean Params.postHigh; simp [binPolicy]
        field_simp; ring
      rw [this]
  rw [t1, p0]
  set q := (1 - x) * P.ρ0 + (1 - P.ρ0)
  have hm : P.ωl + (1 - x) * P.ρ0 * (P.ωh - P.ωl) / q - P.ωh = -((1 - P.ρ0) * (P.ωh - P.ωl) / q) := by
    field_simp; simp only [q]; ring
  rw [hm]
  generalize Φ P lam (P.ωl + (1 - x) * P.ρ0 * (P.ωh - P.ωl) / q) = F
  generalize Φ P lam P.ωh = Fh
  have hne : P.ωh - P.ωl ≠ 0 := (sub_pos.2 hlh).ne'
  have hne2 : 1 - P.ρ0 ≠ 0 := (sub_pos.2 hρ1).ne'
  field_simp
  simp only [q]; ring

lemma chord_P (P : Params) (hS : P.Standing) (lam b μ e : ℝ) (hb : 0 < b) (hμ : 0 < μ) (he : 0 < e)
    (hμb : μ ≠ b) (heb : e ≠ b)
    (heq : e * (P.κ * (P.γ * lam + 2 * P.κ * b * (2 * lam - 1))) =
      P.γ * (P.γ * (5 * lam - 4) + 2 * P.κ * b * (lam - 1))) :
    ((Φ P lam μ - Φ P lam b) / (μ - b) - (Φ P lam e - Φ P lam b) / (e - b)) * (2 * P.γ * (P.γ + b * P.κ))
      = P.κ * (2 - 3 * lam) * (P.cStar μ - P.cStar e) ^ 2 := by
  obtain ⟨hγ, hγe, hhi, hlohi⟩ := std_facts P hS
  have hκ := hS.2.2.2.2.2.2.2.1
  have hlo : P.cLo = P.cHi - P.γ := by rw [hγe]; ring
  have hΦ : ∀ u, Φ P lam u = lam * ((u*P.κ*P.cHi/(P.γ+u*P.κ)) ^ 2 - (P.cHi - P.γ) ^ 2) / (2 * P.γ) +
      (1 - lam) * (u*P.κ*P.cHi/(P.γ+u*P.κ)) * (P.cHi - (u*P.κ*P.cHi/(P.γ+u*P.κ))) / P.γ := by
    intro u; unfold Φ; rw [hlo]; rfl
  have hc : ∀ u, P.cStar u = u*P.κ*P.cHi/(P.γ+u*P.κ) := fun u => rfl
  simp only [hΦ, hc]
  exact chord_core P.κ P.γ P.cHi b lam μ e hκ hγ hb hμ he hμb heb heq

lemma cStar_inj (P : Params) (hS : P.Standing) (μ e : ℝ) (hμ : 0 < μ) (he : 0 < e)
    (h : P.cStar μ = P.cStar e) : μ = e := by
  obtain ⟨hγ, hγe, hhi, hlohi⟩ := std_facts P hS
  have hκ := hS.2.2.2.2.2.2.2.1
  have hc : ∀ u, P.cStar u = u*P.κ*P.cHi/(P.γ+u*P.κ) := fun u => rfl
  rw [hc, hc, div_eq_div_iff (by positivity) (by positivity)] at h
  have h2 : (μ - e) * (P.κ * P.cHi * P.γ) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · linarith
  · exfalso; have : 0 < P.κ * P.cHi * P.γ := by positivity
    linarith

lemma lam2_Q (P : Params) (hS : P.Standing) (lam : ℝ) (h0 : 0 ≤ lam) (h : lam < P.lam2) :
    lam < 1 / 2 ∧ 0 < 2 * P.ωl * P.ωh * (1 - 2 * lam) * P.κ ^ 2 -
      (lam * P.ωh + 2 * (1 - lam) * P.ωl) * P.κ * P.γ - (4 - 5 * lam) * P.γ ^ 2 := by
  obtain ⟨hγ, hγe, hhi, hlohi⟩ := std_facts P hS
  obtain ⟨hωl, hlh, hh1, _, _, _, _, hκ, _⟩ := hS
  have hωh : 0 < P.ωh := by linarith
  obtain ⟨l, hl, hlt⟩ := exists_lt_of_lt_csSup (Set.insert_nonempty _ _) h
  rcases hl with rfl | ⟨⟨hl0, hl1⟩, hG⟩
  · linarith
  refine ⟨by linarith, ?_⟩
  set R := P.κ / P.γ with hR
  have hRpos : 0 < R := by positivity
  set cc := (4 - 5 * l) / (2 * (1 - 2 * l) * P.ωh * P.ωl)
  set bb := (l * P.ωh + 2 * (1 - l) * P.ωl) / (4 * (1 - 2 * l) * P.ωh * P.ωl)
  have hl12 : 0 < 1 - 2 * l := by linarith
  have hcc : 0 ≤ cc := by apply div_nonneg <;> [linarith; positivity]
  have hG2 : P.G2 l = Real.sqrt (cc + bb ^ 2) + bb := rfl
  rw [hG2] at hG
  have hsq := Real.sq_sqrt (show 0 ≤ cc + bb ^ 2 by positivity)
  have hs0 := Real.sqrt_nonneg (cc + bb ^ 2)
  have hQ0 : 0 ≤ R ^ 2 - 2 * bb * R - cc := by nlinarith
  set A := 2 * (1 - 2 * l) * P.ωh * P.ωl
  have hA : 0 < A := by positivity
  have hAc : A * cc = 4 - 5 * l := by simp only [A, cc]; field_simp
  have hAb : A * (2 * bb) = l * P.ωh + 2 * (1 - l) * P.ωl := by simp only [A, bb]; field_simp; ring
  have hQl : 0 ≤ 2 * P.ωl * P.ωh * (1 - 2 * l) * R ^ 2 - (l * P.ωh + 2 * (1 - l) * P.ωl) * R - (4 - 5 * l) := by
    have := mul_nonneg hA.le hQ0
    rw [← hAc, ← hAb]; nlinarith
  set Ql := 2 * P.ωl * P.ωh * (1 - 2 * l) * R ^ 2 - (l * P.ωh + 2 * (1 - l) * P.ωl) * R - (4 - 5 * l)
  set E := 4 * P.ωl * P.ωh * R ^ 2 + (P.ωh - 2 * P.ωl) * R - 5
  have hE1 : (1 - 2 * l) * E = 2 * Ql + (P.ωh + 2 * P.ωl) * R + 3 := by simp only [E, Ql]; ring
  have hE : 0 < E := by
    by_contra hc; push Not at hc
    have : (1 - 2 * l) * E ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hl12.le hc
    nlinarith
  have hQlam : 0 < 2 * P.ωl * P.ωh * (1 - 2 * lam) * R ^ 2 - (lam * P.ωh + 2 * (1 - lam) * P.ωl) * R - (4 - 5 * lam) := by
    have : 2 * P.ωl * P.ωh * (1 - 2 * lam) * R ^ 2 - (lam * P.ωh + 2 * (1 - lam) * P.ωl) * R - (4 - 5 * lam)
        = Ql + (l - lam) * E := by simp only [E, Ql]; ring
    rw [this]; nlinarith [mul_pos (sub_pos.2 hlt) hE]
  have hfin : (2 * P.ωl * P.ωh * (1 - 2 * lam) * R ^ 2 - (lam * P.ωh + 2 * (1 - lam) * P.ωl) * R - (4 - 5 * lam)) * P.γ ^ 2
      = 2 * P.ωl * P.ωh * (1 - 2 * lam) * P.κ ^ 2 - (lam * P.ωh + 2 * (1 - lam) * P.ωl) * P.κ * P.γ - (4 - 5 * lam) * P.γ ^ 2 := by
    rw [hR]; field_simp
  rw [← hfin]; positivity

lemma lam3_Q (P : Params) (hS : P.Standing) (lam : ℝ) (h1 : lam ≤ 1) (h : P.lam3 < lam) :
    4 / 5 < lam ∧ 2 * P.ωl * P.ωh * (2 * lam - 1) * P.κ ^ 2 +
      (2 * (1 - lam) * P.ωh + lam * P.ωl) * P.κ * P.γ - (5 * lam - 4) * P.γ ^ 2 < 0 := by
  obtain ⟨hγ, hγe, hhi, hlohi⟩ := std_facts P hS
  obtain ⟨hωl, hlh, hh1, _, _, _, _, hκ, _⟩ := hS
  have hωh : 0 < P.ωh := by linarith
  obtain ⟨l, hl, hlt⟩ := exists_lt_of_csInf_lt (Set.insert_nonempty _ _) h
  rcases hl with rfl | ⟨⟨hl0, hl1⟩, hG⟩
  · linarith
  refine ⟨by linarith, ?_⟩
  set R := P.κ / P.γ with hR
  have hRpos : 0 < R := by positivity
  set cc := (5 * l - 4) / (2 * (2 * l - 1) * P.ωh * P.ωl)
  set bb := (2 * (1 - l) * P.ωh + l * P.ωl) / (4 * (2 * l - 1) * P.ωh * P.ωl)
  have hl12 : 0 < 2 * l - 1 := by linarith
  have hcc : 0 ≤ cc := by apply div_nonneg <;> [linarith; positivity]
  have hbb : 0 ≤ bb := by apply div_nonneg <;> [nlinarith; positivity]
  have hG1 : P.G1 l = Real.sqrt (cc + bb ^ 2) - bb := rfl
  rw [hG1] at hG
  have hsq := Real.sq_sqrt (show 0 ≤ cc + bb ^ 2 by positivity)
  have hs0 := Real.sqrt_nonneg (cc + bb ^ 2)
  have hQ0 : R ^ 2 + 2 * bb * R - cc ≤ 0 := by nlinarith
  set A := 2 * (2 * l - 1) * P.ωh * P.ωl
  have hA : 0 < A := by positivity
  have hAc : A * cc = 5 * l - 4 := by simp only [A, cc]; field_simp
  have hAb : A * (2 * bb) = 2 * (1 - l) * P.ωh + l * P.ωl := by simp only [A, bb]; field_simp; ring
  have hQl : 2 * P.ωl * P.ωh * (2 * l - 1) * R ^ 2 + (2 * (1 - l) * P.ωh + l * P.ωl) * R - (5 * l - 4) ≤ 0 := by
    have := mul_nonpos_of_nonneg_of_nonpos hA.le hQ0
    rw [← hAc, ← hAb]; nlinarith
  set Ql := 2 * P.ωl * P.ωh * (2 * l - 1) * R ^ 2 + (2 * (1 - l) * P.ωh + l * P.ωl) * R - (5 * l - 4)
  set E := 4 * P.ωl * P.ωh * R ^ 2 + (P.ωl - 2 * P.ωh) * R - 5
  have hE1 : (2 * l - 1) * E = 2 * Ql - (2 * P.ωh + P.ωl) * R - 3 := by simp only [E, Ql]; ring
  have hE : E < 0 := by
    by_contra hc; push Not at hc
    have : 0 ≤ (2 * l - 1) * E := mul_nonneg hl12.le hc
    nlinarith
  have hQlam : 2 * P.ωl * P.ωh * (2 * lam - 1) * R ^ 2 + (2 * (1 - lam) * P.ωh + lam * P.ωl) * R - (5 * lam - 4) < 0 := by
    have : 2 * P.ωl * P.ωh * (2 * lam - 1) * R ^ 2 + (2 * (1 - lam) * P.ωh + lam * P.ωl) * R - (5 * lam - 4)
        = Ql + (lam - l) * E := by simp only [E, Ql]; ring
    rw [this]; nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 hlt) hE]
  have hfin : (2 * P.ωl * P.ωh * (2 * lam - 1) * R ^ 2 + (2 * (1 - lam) * P.ωh + lam * P.ωl) * R - (5 * lam - 4)) * P.γ ^ 2
      = 2 * P.ωl * P.ωh * (2 * lam - 1) * P.κ ^ 2 + (2 * (1 - lam) * P.ωh + lam * P.ωl) * P.κ * P.γ - (5 * lam - 4) * P.γ ^ 2 := by
    rw [hR]; field_simp
  rw [← hfin]; exact mul_neg_of_neg_of_pos hQlam (by positivity)


lemma ex_main (P : Params) (hS : P.Standing) (lam pl : ℝ) (h0 : 0 ≤ lam) (hl2 : lam < P.lam2)
    (hμ : P.μ0 < P.μEX lam) (hopt : P.IsOptimalPolicy lam (binPolicy pl 1)) :
    lam < 1 / 2 ∧ P.μEX lam * (P.κ * (P.γ * lam + 2 * P.κ * P.ωl * (2 * lam - 1))) =
      P.γ * (P.γ * (5 * lam - 4) + 2 * P.κ * P.ωl * (lam - 1)) ∧
    0 ≤ pl ∧ pl ≤ 1 ∧ P.postMean (binPolicy pl 1) 1 = P.μEX lam := by
  obtain ⟨hγ, hγe, hhi, hlohi⟩ := std_facts P hS
  have hS0 := hS
  obtain ⟨hωl, hlh, hh1, hρ0, hρ1, _, _, hκ, _⟩ := hS0
  obtain ⟨hlt, hpoly⟩ := lam2_Q P hS lam h0 hl2
  set e := P.μEX lam with he_def
  have hμ0 : P.μ0 - P.ωl = P.ρ0 * (P.ωh - P.ωl) := by unfold Params.μ0; ring
  have hd : 0 < P.ρ0 * (P.ωh - P.ωl) := mul_pos hρ0 (by linarith)
  have hne : P.ωh - P.ωl ≠ 0 := (sub_pos.2 hlh).ne'
  -- the relation for e
  have hD : 2 * P.κ * P.ωl * (2 * lam - 1) + P.γ * lam ≠ 0 := by
    intro hD0
    have : e = P.ωl := by
      rw [he_def]; unfold Params.μEX Params.ρEX; rw [hD0]; simp
    linarith
  have heq : e * (P.κ * (P.γ * lam + 2 * P.κ * P.ωl * (2 * lam - 1))) =
      P.γ * (P.γ * (5 * lam - 4) + 2 * P.κ * P.ωl * (lam - 1)) := by
    have hρ : P.ρEX lam * (P.κ * (P.ωh - P.ωl) * (2 * P.κ * P.ωl * (2 * lam - 1) + P.γ * lam)) =
        (2 * P.κ * P.ωl * (1 - 2 * lam) - P.γ * (4 - 5 * lam)) * (P.κ * P.ωl + P.γ) := by
      unfold Params.ρEX
      exact div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero hκ.ne' hne) hD)
    have he2 : e = P.ρEX lam * (P.ωh - P.ωl) + P.ωl := rfl
    rw [he2]
    linear_combination hρ
  have hepos : 0 < e := by nlinarith
  have hDneg : P.γ * lam + 2 * P.κ * P.ωl * (2 * lam - 1) < 0 := by
    by_contra hc; push Not at hc
    have h1 : 0 ≤ e * (P.κ * (P.γ * lam + 2 * P.κ * P.ωl * (2 * lam - 1))) := by positivity
    have h2 : P.γ * (P.γ * (5 * lam - 4) + 2 * P.κ * P.ωl * (lam - 1)) < 0 := by
      apply mul_neg_of_pos_of_neg hγ; nlinarith
    linarith
  have heh : e < P.ωh := by
    by_contra hc; push Not at hc
    have : e * (P.κ * (P.γ * lam + 2 * P.κ * P.ωl * (2 * lam - 1))) ≤
        P.ωh * (P.κ * (P.γ * lam + 2 * P.κ * P.ωl * (2 * lam - 1))) :=
      mul_le_mul_of_nonpos_right hc (mul_nonpos_of_nonneg_of_nonpos hκ.le hDneg.le)
    nlinarith
  refine ⟨hlt, heq, ?_⟩
  obtain ⟨hπ, a, ha, hmin⟩ := hopt
  have hpl0 : 0 ≤ pl := by have := hπ.1 0 0; simpa [binPolicy] using this
  have hpl1 : pl ≤ 1 := by have := hπ.1 0 1; simp [binPolicy] at this; linarith
  refine ⟨hpl0, hpl1, ?_⟩
  -- the comparison policy
  set qs := P.ρ0 * (P.ωh - P.ωl) / (e - P.ωl) with hqs
  have hel : 0 < e - P.ωl := by linarith
  have hqs1 : qs ≤ 1 := by rw [hqs, div_le_one hel]; linarith
  have hqs0 : P.ρ0 ≤ qs := by
    rw [hqs, le_div_iff₀ hel]; nlinarith
  set xs := (1 - qs) / (1 - P.ρ0) with hxs
  have hρ1' : 0 < 1 - P.ρ0 := by linarith
  have hxs0 : 0 ≤ xs := div_nonneg (by linarith) hρ1'.le
  have hxs1 : xs ≤ 1 := by rw [hxs, div_le_one hρ1']; linarith
  have hqx : P.ρ0 + (1 - P.ρ0) * (1 - xs) = qs := by rw [hxs]; field_simp; ring
  have hmxs : P.postMean (binPolicy xs 1) 1 = e := by
    rw [mh_eq P hS xs hxs1, hqx, hqs]; field_simp; ring
  have hcmp := hmin (Fin 2) (binPolicy xs 1) (fun c μ => if c ≤ P.cStar μ then (1 : ℝ) else 0)
    (binPolicy_isPolicy xs 1 hxs0 hxs1 zero_le_one le_rfl) (a0_bne P hS)
  rw [ex_cost P hS lam pl hpl0 hpl1 a ha, ex_cost P hS lam xs hxs0 hxs1 _ (a0_bne P hS), hmxs] at hcmp
  set μ := P.postMean (binPolicy pl 1) 1
  have hμv : μ = P.ωl + P.ρ0 * (P.ωh - P.ωl) / (P.ρ0 + (1 - P.ρ0) * (1 - pl)) := mh_eq P hS pl hpl1
  have hμl : P.ωl < μ := by
    rw [hμv]; have : 0 < P.ρ0 + (1 - P.ρ0) * (1 - pl) := by nlinarith
    have := div_pos hd this; linarith
  have hSle : (Φ P lam μ - Φ P lam P.ωl) / (μ - P.ωl) ≤ (Φ P lam e - Φ P lam P.ωl) / (e - P.ωl) := by
    have := le_of_add_le_add_left hcmp
    exact le_of_mul_le_mul_left this hd
  have hch := chord_P P hS lam P.ωl μ e hωl (by linarith) hepos (ne_of_gt hμl) (ne_of_gt hel |>.symm |> fun h => by
    intro h'; exact absurd h' (by linarith)) heq
  have hpos : 0 < 2 * P.γ * (P.γ + P.ωl * P.κ) := by positivity
  have hsq : P.κ * (2 - 3 * lam) * (P.cStar μ - P.cStar e) ^ 2 ≤ 0 := by
    rw [← hch]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
  have hk3 : 0 < P.κ * (2 - 3 * lam) := mul_pos hκ (by linarith)
  have : (P.cStar μ - P.cStar e) ^ 2 = 0 := by
    apply le_antisymm _ (sq_nonneg _)
    have h' : P.κ * (2 - 3 * lam) * (P.cStar μ - P.cStar e) ^ 2 ≤ P.κ * (2 - 3 * lam) * 0 := by
      rw [mul_zero]; exact hsq
    exact le_of_mul_le_mul_left h' hk3
  have hcs : P.cStar μ = P.cStar e := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this; linarith
  exact cStar_inj P hS μ e (by linarith) hepos hcs


lemma dp_main (P : Params) (hS : P.Standing) (lam ph : ℝ) (h1 : lam ≤ 1) (hl3 : P.lam3 < lam)
    (hμ : P.μDP lam < P.μ0) (hopt : P.IsOptimalPolicy lam (binPolicy 1 ph)) :
    4 / 5 < lam ∧ P.μDP lam * (P.κ * (P.γ * lam + 2 * P.κ * P.ωh * (2 * lam - 1))) =
      P.γ * (P.γ * (5 * lam - 4) + 2 * P.κ * P.ωh * (lam - 1)) ∧ P.ωl < P.μDP lam ∧
    0 ≤ ph ∧ ph ≤ 1 ∧ P.postMean (binPolicy 1 ph) 0 = P.μDP lam := by
  obtain ⟨hγ, hγe, hhi, hlohi⟩ := std_facts P hS
  have hS0 := hS
  obtain ⟨hωl, hlh, hh1, hρ0, hρ1, _, _, hκ, _⟩ := hS0
  have hωh : 0 < P.ωh := by linarith
  obtain ⟨hlt, hpoly⟩ := lam3_Q P hS lam h1 hl3
  set e := P.μDP lam with he_def
  have hμ0 : P.μ0 - P.ωl = P.ρ0 * (P.ωh - P.ωl) := by unfold Params.μ0; ring
  have hne : P.ωh - P.ωl ≠ 0 := (sub_pos.2 hlh).ne'
  have hDpos : 0 < 2 * P.κ * P.ωh * (2 * lam - 1) + P.γ * lam := by
    have : 0 < 2 * lam - 1 := by linarith
    have : 0 < lam := by linarith
    positivity
  have heq : e * (P.κ * (P.γ * lam + 2 * P.κ * P.ωh * (2 * lam - 1))) =
      P.γ * (P.γ * (5 * lam - 4) + 2 * P.κ * P.ωh * (lam - 1)) := by
    have hρ : P.ρDP lam * (P.κ * (P.ωh - P.ωl) * (2 * P.κ * P.ωh * (2 * lam - 1) + P.γ * lam)) =
        P.γ ^ 2 * (5 * lam - 4) - 2 * P.κ ^ 2 * P.ωl * P.ωh * (2 * lam - 1) -
          P.γ * P.κ * (2 * (1 - lam) * P.ωh + lam * P.ωl) := by
      unfold Params.ρDP
      exact div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero hκ.ne' hne) hDpos.ne')
    have he2 : e = P.ρDP lam * (P.ωh - P.ωl) + P.ωl := rfl
    rw [he2]
    linear_combination hρ
  have hel : P.ωl < e := by
    by_contra hc; push Not at hc
    have : e * (P.κ * (P.γ * lam + 2 * P.κ * P.ωh * (2 * lam - 1))) ≤
        P.ωl * (P.κ * (P.γ * lam + 2 * P.κ * P.ωh * (2 * lam - 1))) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hκ.le (by linarith))
    nlinarith
  have hepos : 0 < e := by linarith
  refine ⟨hlt, heq, hel, ?_⟩
  obtain ⟨hπ, a, ha, hmin⟩ := hopt
  have hph0 : 0 ≤ ph := by have := hπ.1 1 1; simpa [binPolicy] using this
  have hph1 : ph ≤ 1 := by have := hπ.1 1 0; simp [binPolicy] at this; linarith
  refine ⟨hph0, hph1, ?_⟩
  have hρ1' : 0 < 1 - P.ρ0 := by linarith
  have hhe : 0 < P.ωh - e := by unfold Params.μ0 at hμ; nlinarith
  set zs := (e - P.ωl) * (1 - P.ρ0) / (P.ωh - e) with hzs
  have hzs0 : 0 ≤ zs := div_nonneg (mul_nonneg (by linarith) hρ1'.le) hhe.le
  have hzs1 : zs ≤ P.ρ0 := by
    rw [hzs, div_le_iff₀ hhe]; unfold Params.μ0 at hμ; nlinarith
  set xs := 1 - zs / P.ρ0 with hxs
  have hxs0 : 0 ≤ xs := by rw [hxs, sub_nonneg, div_le_one hρ0]; exact hzs1
  have hxs1 : xs ≤ 1 := by rw [hxs]; have := div_nonneg hzs0 hρ0.le; linarith
  have hz : (1 - xs) * P.ρ0 = zs := by rw [hxs]; field_simp; ring
  have hmxs : P.postMean (binPolicy 1 xs) 0 = e := by
    rw [ml_eq P hS xs hxs1, hz]
    have hden : zs + (1 - P.ρ0) = (1 - P.ρ0) * (P.ωh - P.ωl) / (P.ωh - e) := by
      rw [hzs]; field_simp; ring
    have hden' : zs * (P.ωh - P.ωl) / (zs + (1 - P.ρ0)) = e - P.ωl := by
      rw [hden, hzs]; field_simp
    linarith [hden']
  have hcmp := hmin (Fin 2) (binPolicy 1 xs) (fun c μ => if c ≤ P.cStar μ then (1 : ℝ) else 0)
    (binPolicy_isPolicy 1 xs zero_le_one le_rfl hxs0 hxs1) (a0_bne P hS)
  rw [dp_cost P hS lam ph hph0 hph1 a ha, dp_cost P hS lam xs hxs0 hxs1 _ (a0_bne P hS), hmxs] at hcmp
  set μ := P.postMean (binPolicy 1 ph) 0
  have hμv : μ = P.ωl + (1 - ph) * P.ρ0 * (P.ωh - P.ωl) / ((1 - ph) * P.ρ0 + (1 - P.ρ0)) :=
    ml_eq P hS ph hph1
  have hμm := postMean_mem P hS _ (binPolicy_isPolicy 1 ph zero_le_one le_rfl hph0 hph1) 0
  have hμh : μ < P.ωh := by
    rw [hμv]
    have hq : 0 < (1 - ph) * P.ρ0 + (1 - P.ρ0) := by nlinarith
    rw [← sub_pos]
    have : P.ωh - (P.ωl + (1 - ph) * P.ρ0 * (P.ωh - P.ωl) / ((1 - ph) * P.ρ0 + (1 - P.ρ0))) =
        (1 - P.ρ0) * (P.ωh - P.ωl) / ((1 - ph) * P.ρ0 + (1 - P.ρ0)) := by field_simp; ring
    rw [this]; exact div_pos (mul_pos hρ1' (by linarith)) hq
  have hd : 0 < (1 - P.ρ0) * (P.ωh - P.ωl) := mul_pos hρ1' (by linarith)
  have hSge : (Φ P lam e - Φ P lam P.ωh) / (e - P.ωh) ≤ (Φ P lam μ - Φ P lam P.ωh) / (μ - P.ωh) := by
    have := (sub_le_sub_iff_left _).1 hcmp
    exact le_of_mul_le_mul_left this hd
  have hch := chord_P P hS lam P.ωh μ e hωh (lt_of_lt_of_le hωl hμm.1) hepos (ne_of_lt hμh)
    (ne_of_lt (show e < P.ωh by linarith)) heq
  have hpos : 0 < 2 * P.γ * (P.γ + P.ωh * P.κ) := by positivity
  have hk3 : 0 < P.κ * (3 * lam - 2) := mul_pos hκ (by linarith)
  have : (P.cStar μ - P.cStar e) ^ 2 = 0 := by
    apply le_antisymm _ (sq_nonneg _)
    have h' : P.κ * (3 * lam - 2) * (P.cStar μ - P.cStar e) ^ 2 ≤ P.κ * (3 * lam - 2) * 0 := by
      rw [mul_zero]
      have : P.κ * (3 * lam - 2) * (P.cStar μ - P.cStar e) ^ 2 =
        -(P.κ * (2 - 3 * lam) * (P.cStar μ - P.cStar e) ^ 2) := by ring
      rw [this, ← hch]
      have : 0 ≤ ((Φ P lam μ - Φ P lam P.ωh) / (μ - P.ωh) - (Φ P lam e - Φ P lam P.ωh) / (e - P.ωh)) *
        (2 * P.γ * (P.γ + P.ωh * P.κ)) := mul_nonneg (by linarith) hpos.le
      linarith
    exact le_of_mul_le_mul_left h' hk3
  have hcs : P.cStar μ = P.cStar e := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this; linarith
  exact cStar_inj P hS μ e (lt_of_lt_of_le hωl hμm.1) hepos hcs


lemma ex_mono (κ g g' wl lam e e' : ℝ) (hκ : 0 < κ) (hg : 0 < g) (hgg : g < g') (h0 : 0 ≤ lam)
    (hl : lam < 1 / 2) (hwl : 0 < wl) (he : 0 < e) (he' : 0 < e')
    (r : e * (κ * (g * lam + 2 * κ * wl * (2 * lam - 1))) = g * (g * (5 * lam - 4) + 2 * κ * wl * (lam - 1)))
    (r' : e' * (κ * (g' * lam + 2 * κ * wl * (2 * lam - 1))) =
      g' * (g' * (5 * lam - 4) + 2 * κ * wl * (lam - 1))) : e < e' := by
  set B := -(κ * (g * lam + 2 * κ * wl * (2 * lam - 1)))
  set B' := -(κ * (g' * lam + 2 * κ * wl * (2 * lam - 1)))
  have ha : 0 < 4 - 5 * lam := by linarith
  have hb : 0 < 1 - lam := by linarith
  have hN : 0 < g * (g * (4 - 5 * lam) + 2 * κ * wl * (1 - lam)) := by positivity
  have hN' : g * (g * (4 - 5 * lam) + 2 * κ * wl * (1 - lam)) <
      g' * (g' * (4 - 5 * lam) + 2 * κ * wl * (1 - lam)) := by
    have key : g' * (g' * (4 - 5 * lam) + 2 * κ * wl * (1 - lam)) - g * (g * (4 - 5 * lam) + 2 * κ * wl * (1 - lam))
        = (g' - g) * ((g' + g) * (4 - 5 * lam) + 2 * κ * wl * (1 - lam)) := by ring
    have : 0 < (g' - g) * ((g' + g) * (4 - 5 * lam) + 2 * κ * wl * (1 - lam)) := by
      have : 0 < g' - g := by linarith
      have : 0 < g' + g := by linarith
      positivity
    linarith
  have rB : e * B = g * (g * (4 - 5 * lam) + 2 * κ * wl * (1 - lam)) := by simp only [B]; linear_combination -r
  have rB' : e' * B' = g' * (g' * (4 - 5 * lam) + 2 * κ * wl * (1 - lam)) := by
    simp only [B']; linear_combination -r'
  have hB' : 0 < B' := by
    by_contra hc; push Not at hc
    have : e' * B' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he'.le hc
    linarith
  have hBB : B' ≤ B := by
    have : B - B' = κ * lam * (g' - g) := by simp only [B, B']; ring
    have : 0 ≤ κ * lam * (g' - g) := mul_nonneg (mul_nonneg hκ.le h0) (by linarith)
    linarith
  have h5 := mul_le_mul_of_nonneg_left hBB he.le
  have : (e' - e) * B' > 0 := by
    have : (e' - e) * B' = e' * B' - e * B' := by ring
    linarith
  exact sub_pos.1 (pos_of_mul_pos_left this hB'.le)

lemma dp_mono (κ g g' wh lam e e' : ℝ) (hκ : 0 < κ) (hg : 0 < g) (hgg : g < g')
    (hl : 4 / 5 < lam) (hwh : 0 < wh) (he : 0 < e)
    (r : e * (κ * (g * lam + 2 * κ * wh * (2 * lam - 1))) = g * (g * (5 * lam - 4) + 2 * κ * wh * (lam - 1)))
    (r' : e' * (κ * (g' * lam + 2 * κ * wh * (2 * lam - 1))) =
      g' * (g' * (5 * lam - 4) + 2 * κ * wh * (lam - 1))) : e < e' := by
  set D := g * lam + 2 * κ * wh * (2 * lam - 1)
  set D' := g' * lam + 2 * κ * wh * (2 * lam - 1)
  set N := g * (5 * lam - 4) + 2 * κ * wh * (lam - 1)
  set N' := g' * (5 * lam - 4) + 2 * κ * wh * (lam - 1)
  have hD : 0 < D := by
    have : 0 < 2 * lam - 1 := by linarith
    have : 0 < lam := by linarith
    positivity
  have hD' : 0 < D' := by
    have : 0 < 2 * lam - 1 := by linarith
    have : 0 < lam := by linarith
    have : 0 < g' := by linarith
    positivity
  have hN : 0 < N := by
    have h1 : 0 < e * (κ * D) := by positivity
    rw [r] at h1
    exact pos_of_mul_pos_right h1 hg.le
  have hcross : N' * D - N * D' = (g' - g) * (2 * κ * wh * (3 * lam - 2) ^ 2) := by
    simp only [N, N', D, D']; ring
  have hc0 : 0 ≤ N' * D - N * D' := by
    rw [hcross]; apply mul_nonneg (by linarith); positivity
  have key : (e' - e) * (κ * D * D') = g' * (N' * D - N * D') + (g' - g) * (N * D') := by
    have r1 : e * (κ * D) = g * N := r
    have r2 : e' * (κ * D') = g' * N' := r'
    linear_combination D * r2 - D' * r1
  have hpos : 0 < (e' - e) * (κ * D * D') := by
    rw [key]
    have : 0 < (g' - g) * (N * D') := mul_pos (by linarith) (mul_pos hN hD')
    have : 0 ≤ g' * (N' * D - N * D') := mul_nonneg (by linarith) hc0
    linarith
  have : 0 < κ * D * D' := by positivity
  exact sub_pos.1 (pos_of_mul_pos_left hpos this.le)

end PandemicThm2Aux

open PandemicInfo.Inequality PandemicThm2Aux in
theorem solution (P : Params) (σ' : ℝ) (hσ : P.σ < σ') (hS : P.Standing)
    (hS' : ({ P with σ := σ' } : Params).Standing) :
    (({ P with σ := σ' } : Params).lam1 ≤ P.lam1 ∧ ({ P with σ := σ' } : Params).lam2 ≤ P.lam2 ∧
      ({ P with σ := σ' } : Params).lam3 ≤ P.lam3 ∧ ({ P with σ := σ' } : Params).lam4 ≤ P.lam4) ∧
    (∀ lam pl pl' : ℝ, 0 ≤ lam → lam ≤ 1 →
      P.lam1 < lam → lam < P.lam2 → P.μ0 < P.μEX lam →
      ({ P with σ := σ' } : Params).lam1 < lam → lam < ({ P with σ := σ' } : Params).lam2 →
      ({ P with σ := σ' } : Params).μ0 < ({ P with σ := σ' } : Params).μEX lam →
      P.IsOptimalPolicy lam (binPolicy pl 1) →
      ({ P with σ := σ' } : Params).IsOptimalPolicy lam (binPolicy pl' 1) →
      1 - pl' < 1 - pl) ∧
    (∀ lam ph ph' : ℝ, 0 ≤ lam → lam ≤ 1 →
      P.lam3 < lam → lam < P.lam4 → P.μDP lam < P.μ0 →
      ({ P with σ := σ' } : Params).lam3 < lam → lam < ({ P with σ := σ' } : Params).lam4 →
      ({ P with σ := σ' } : Params).μDP lam < ({ P with σ := σ' } : Params).μ0 →
      P.IsOptimalPolicy lam (binPolicy 1 ph) →
      ({ P with σ := σ' } : Params).IsOptimalPolicy lam (binPolicy 1 ph') →
      1 - ph < 1 - ph') := by
  obtain ⟨hγ, _, _, _⟩ := std_facts P hS
  have hS0 := hS
  obtain ⟨hωl, hlh, hh1, hρ0, hρ1, hσ0, _, hκ, _⟩ := hS0
  have hγγ : P.γ < ({ P with σ := σ' } : Params).γ := by
    show P.σ * 2 * Real.sqrt 3 < σ' * 2 * Real.sqrt 3
    have : 0 < Real.sqrt 3 := by positivity
    nlinarith
  have hμ0pos : 0 < P.μ0 := by unfold Params.μ0; nlinarith
  refine ⟨part1 P σ' hσ hS, ?_, ?_⟩
  · intro lam pl pl' h0 h1 _ hl2 hμ _ hl2' hμ' hopt hopt'
    obtain ⟨hlt, r, hpl0, hpl1, hm⟩ := ex_main P hS lam pl h0 hl2 hμ hopt
    obtain ⟨_, r', hpl0', hpl1', hm'⟩ := ex_main _ hS' lam pl' h0 hl2' hμ' hopt'
    have hlt' : P.μEX lam < ({ P with σ := σ' } : Params).μEX lam :=
      ex_mono P.κ P.γ ({ P with σ := σ' } : Params).γ P.ωl lam _ _ hκ hγ hγγ h0 hlt hωl
        (by linarith) (lt_trans hμ0pos hμ') r r'
    have m1 := mh_eq P hS pl hpl1
    have m2 : ({ P with σ := σ' } : Params).postMean (binPolicy pl' 1) 1 =
        P.ωl + P.ρ0 * (P.ωh - P.ωl) / (P.ρ0 + (1 - P.ρ0) * (1 - pl')) := mh_eq _ hS' pl' hpl1'
    rw [← hm, ← hm', m1, m2] at hlt'
    have hd : 0 < P.ρ0 * (P.ωh - P.ωl) := mul_pos hρ0 (by linarith)
    have hρ1' : 0 < 1 - P.ρ0 := by linarith
    have hq : 0 < P.ρ0 + (1 - P.ρ0) * (1 - pl) := by
      have := mul_nonneg hρ1'.le (sub_nonneg.2 hpl1); linarith
    have hq' : 0 < P.ρ0 + (1 - P.ρ0) * (1 - pl') := by
      have := mul_nonneg hρ1'.le (sub_nonneg.2 hpl1'); linarith
    have := (div_lt_div_iff_of_pos_left hd hq hq').1 (by linarith)
    have h6 : (1 - P.ρ0) * (1 - pl') < (1 - P.ρ0) * (1 - pl) := by linarith
    exact lt_of_mul_lt_mul_left h6 hρ1'.le
  · intro lam ph ph' h0 h1 hl3 _ hμ hl3' _ hμ' hopt hopt'
    obtain ⟨hlt, r, hel, hph0, hph1, hm⟩ := dp_main P hS lam ph h1 hl3 hμ hopt
    obtain ⟨_, r', _, hph0', hph1', hm'⟩ := dp_main _ hS' lam ph' h1 hl3' hμ' hopt'
    have hlt' : P.μDP lam < ({ P with σ := σ' } : Params).μDP lam :=
      dp_mono P.κ P.γ ({ P with σ := σ' } : Params).γ P.ωh lam _ _ hκ hγ hγγ hlt (by linarith)
        (by linarith) r r'
    have m1 := ml_eq P hS ph hph1
    have m2 : ({ P with σ := σ' } : Params).postMean (binPolicy 1 ph') 0 =
        P.ωl + (1 - ph') * P.ρ0 * (P.ωh - P.ωl) / ((1 - ph') * P.ρ0 + (1 - P.ρ0)) := ml_eq _ hS' ph' hph1'
    rw [← hm, ← hm', m1, m2] at hlt'
    have hρ1' : 0 < 1 - P.ρ0 := by linarith
    have hq : 0 < (1 - ph) * P.ρ0 + (1 - P.ρ0) := by
      have := mul_nonneg (sub_nonneg.2 hph1) hρ0.le; linarith
    have hq' : 0 < (1 - ph') * P.ρ0 + (1 - P.ρ0) := by
      have := mul_nonneg (sub_nonneg.2 hph1') hρ0.le; linarith
    have h2 : (1 - ph) * P.ρ0 * (P.ωh - P.ωl) / ((1 - ph) * P.ρ0 + (1 - P.ρ0)) <
        (1 - ph') * P.ρ0 * (P.ωh - P.ωl) / ((1 - ph') * P.ρ0 + (1 - P.ρ0)) := by linarith
    rw [div_lt_div_iff₀ hq hq'] at h2
    have hw : 0 < P.ωh - P.ωl := by linarith
    have h3 : ((1 - ph) * P.ρ0 - (1 - ph') * P.ρ0) * ((1 - P.ρ0) * (P.ωh - P.ωl)) < 0 := by
      have : ((1 - ph) * P.ρ0 - (1 - ph') * P.ρ0) * ((1 - P.ρ0) * (P.ωh - P.ωl)) =
        (1 - ph) * P.ρ0 * (P.ωh - P.ωl) * ((1 - ph') * P.ρ0 + (1 - P.ρ0)) -
          (1 - ph') * P.ρ0 * (P.ωh - P.ωl) * ((1 - ph) * P.ρ0 + (1 - P.ρ0)) := by ring
      linarith
    have h4 : (1 - ph) * P.ρ0 - (1 - ph') * P.ρ0 < 0 := by
      by_contra hc; push Not at hc
      have := mul_nonneg hc (mul_pos hρ1' hw).le; linarith
    have h7 : (1 - ph) * P.ρ0 < (1 - ph') * P.ρ0 := by linarith
    exact lt_of_mul_lt_mul_right h7 hρ0.le
