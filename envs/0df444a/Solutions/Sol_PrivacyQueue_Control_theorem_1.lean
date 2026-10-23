-- Prove2me | solution 1 for PrivacyQueue.Control.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T03:53:23.380154+00:00
-- url     : https://prove2.me/submissions/7c0ab514-b7a1-4df2-b3b8-5c50a09d5b97

import Mathlib
import Definitions.Def_PrivacyQueue_Control_Model

set_option autoImplicit false

namespace PQSolAda

open PrivacyQueue.Control

/-- Effective-load factor `1 + α (σ - 1)`. -/
noncomputable def Ef (P : Params) : ℝ := 1 + P.α * (P.σ - 1)

lemma Ef_pos (P : Params) (hσ : 0 < P.σ) (hα0 : 0 ≤ P.α) (hα1 : P.α ≤ 1) : 0 < Ef P := by
  unfold Ef
  rcases lt_or_eq_of_le hα1 with h | h
  · nlinarith [mul_nonneg hα0 hσ.le]
  · rw [h]; linarith

lemma WH_eq (P : Params) (γ : ℝ) (hμ : P.mu ≠ 0) (hZ : P.mu - P.α * γ * P.lam ≠ 0) :
    WH P γ = 1 / (P.mu - P.α * γ * P.lam) := by
  simp only [WH, Params.queue, PriorityQueue3.waitH, rhoH, RH, BH]
  have h1 : 1 - P.α * γ * P.lam / P.mu = (P.mu - P.α * γ * P.lam) / P.mu := by
    field_simp
  rw [h1]
  field_simp
  try ring

lemma RN_eq (P : Params) (hμ : P.mu ≠ 0) (hσ : P.σ ≠ 0) (hE : Ef P ≠ 0) :
    RN P = (P.α * P.σ ^ 2 + 1 - P.α) / (P.σ * P.mu * Ef P) := by
  unfold RN
  have hd : P.α * (1 / P.mu) + (1 - P.α) * (1 / (P.σ * P.mu)) = Ef P / (P.σ * P.mu) := by
    unfold Ef; field_simp; try ring
  rw [hd]
  unfold Ef at hE ⊢
  field_simp
  try ring

lemma WN_eq (P : Params) (γ : ℝ) (hμ : P.mu ≠ 0) (hσ : P.σ ≠ 0) (hE : Ef P ≠ 0)
    (hZ : P.mu - P.α * γ * P.lam ≠ 0)
    (hX : P.σ * P.mu - P.σ * P.α * γ * P.lam - Ef P * (1 - γ) * P.lam ≠ 0) :
    WN P γ = (P.lam * (P.α * P.σ ^ 2 + (1 - γ) * (1 - P.α)) +
        Ef P * (P.σ * P.mu - P.σ * P.α * γ * P.lam - Ef P * (1 - γ) * P.lam)) /
      (P.σ * (P.σ * P.mu - P.σ * P.α * γ * P.lam - Ef P * (1 - γ) * P.lam) *
        (P.mu - P.α * γ * P.lam)) := by
  simp only [WN, Params.queue, PriorityQueue3.waitN]
  rw [RN_eq P hμ hσ hE]
  have h1 : 1 - rhoH P γ = (P.mu - P.α * γ * P.lam) / P.mu := by
    unfold rhoH; field_simp
  have h2 : 1 - rhoH P γ - rhoN P γ =
      (P.σ * P.mu - P.σ * P.α * γ * P.lam - Ef P * (1 - γ) * P.lam) / (P.σ * P.mu) := by
    unfold rhoH rhoN Ef; field_simp; try ring
  have h3 : rhoH P γ * RH P + rhoN P γ * ((P.α * P.σ ^ 2 + 1 - P.α) / (P.σ * P.mu * Ef P)) =
      P.lam * (P.α * P.σ ^ 2 + (1 - γ) * (1 - P.α)) / (P.σ ^ 2 * P.mu ^ 2) := by
    have hE' := hE
    unfold Ef at hE'
    unfold rhoH rhoN RH Ef; field_simp; try ring
  have hBN : BN P = Ef P / (P.σ * P.mu) := by unfold BN Ef; rfl
  rw [h3, h2, h1, hBN]
  generalize P.σ * P.mu - P.σ * P.α * γ * P.lam - Ef P * (1 - γ) * P.lam = X at hX ⊢
  generalize P.mu - P.α * γ * P.lam = Z at hZ ⊢
  field_simp
  try ring

lemma WL_eq (P : Params) (γ : ℝ) (hμ : P.mu ≠ 0) (hσ : P.σ ≠ 0) (hE : Ef P ≠ 0)
    (hX : P.σ * P.mu - P.σ * P.α * γ * P.lam - Ef P * (1 - γ) * P.lam ≠ 0)
    (hY : P.σ * P.mu - Ef P * P.lam ≠ 0) :
    WL P γ = (P.lam * (P.α * P.σ ^ 2 + 1 - P.α) + (P.σ * P.mu - Ef P * P.lam)) /
      ((P.σ * P.mu - Ef P * P.lam) *
        (P.σ * P.mu - P.σ * P.α * γ * P.lam - Ef P * (1 - γ) * P.lam)) := by
  simp only [WL, Params.queue, PriorityQueue3.waitL]
  rw [RN_eq P hμ hσ hE]
  have h2 : 1 - rhoH P γ - rhoN P γ =
      (P.σ * P.mu - P.σ * P.α * γ * P.lam - Ef P * (1 - γ) * P.lam) / (P.σ * P.mu) := by
    unfold rhoH rhoN Ef; field_simp; try ring
  have h4 : 1 - rhoH P γ - rhoN P γ - rhoL P γ = (P.σ * P.mu - Ef P * P.lam) / (P.σ * P.mu) := by
    unfold rhoH rhoN rhoL Ef; field_simp; try ring
  have h3 : rhoH P γ * RH P + rhoN P γ * ((P.α * P.σ ^ 2 + 1 - P.α) / (P.σ * P.mu * Ef P)) +
      rhoL P γ * RL P = P.lam * (P.α * P.σ ^ 2 + 1 - P.α) / (P.σ ^ 2 * P.mu ^ 2) := by
    have hE' := hE
    unfold Ef at hE'
    unfold rhoH rhoN rhoL RH RL Ef; field_simp; try ring
  rw [h3, h4, h2]
  unfold BL
  generalize P.σ * P.mu - P.σ * P.α * γ * P.lam - Ef P * (1 - γ) * P.lam = X at hX ⊢
  generalize P.σ * P.mu - Ef P * P.lam = Y at hY ⊢
  field_simp
  try ring

/-- Positivity of the cleared denominators under the standing assumptions. -/
lemma facts (P : Params) (hS : P.Standing) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    0 < Ef P ∧ 0 < P.σ * P.mu - Ef P * P.lam ∧ 0 < P.mu - P.α * P.lam ∧
    0 < P.mu - P.α * γ * P.lam ∧
    0 < P.σ * P.mu - P.σ * P.α * γ * P.lam - Ef P * (1 - γ) * P.lam := by
  obtain ⟨hμ, hσ, _, hα0, hα1, hl, hllt, _, _⟩ := hS
  have hE := Ef_pos P hσ hα0 hα1
  have hY : 0 < P.σ * P.mu - Ef P * P.lam := by
    unfold Params.mubar at hllt
    have hE' : 0 < 1 + P.α * (P.σ - 1) := hE
    rw [lt_div_iff₀ hE'] at hllt
    unfold Ef; linarith
  have hZ1 : 0 < P.mu - P.α * P.lam := by
    have h : 0 < P.σ * (P.mu - P.α * P.lam) := by
      unfold Ef at hY
      nlinarith [mul_nonneg hl.le (sub_nonneg.2 hα1)]
    exact pos_of_mul_pos_right h hσ.le
  refine ⟨hE, hY, hZ1, ?_, ?_⟩
  · nlinarith [mul_nonneg (mul_nonneg hα0 hl.le) (sub_nonneg.2 hγ1)]
  · unfold Ef at hY ⊢
    nlinarith [mul_nonneg (mul_nonneg hγ0 hl.le) (sub_nonneg.2 hα1)]

/-- Closed form of the surplus gap between customer control and full disclosure. -/
lemma diff_eq (P : Params) (hS : P.Standing) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    CScontrol P γ - CSdiscl P = (P.σ - 1) *
      (P.c * (1 - γ) ^ 2 * P.α * (1 - P.α) * P.lam ^ 2 *
          (P.mu - P.α * P.lam + P.α * P.lam * P.σ) /
        (P.σ * (P.mu - P.α * γ * P.lam) *
          (P.σ * P.mu - P.σ * P.α * γ * P.lam - Ef P * (1 - γ) * P.lam) *
          (P.mu - P.α * P.lam))) := by
  obtain ⟨hE, hY, hZ1, hZ, hX⟩ := facts P hS γ hγ0 hγ1
  obtain ⟨hμ, hσ, _, _, _, hl, _, _, _⟩ := hS
  have e1 : P.mu - P.α * 1 * P.lam = P.mu - P.α * P.lam := by ring
  have e2 : P.σ * P.mu - P.σ * P.α * 1 * P.lam - Ef P * (1 - 1) * P.lam =
      P.σ * (P.mu - P.α * P.lam) := by ring
  have hZ1' : P.mu - P.α * 1 * P.lam ≠ 0 := by rw [e1]; exact hZ1.ne'
  have hX1' : P.σ * P.mu - P.σ * P.α * 1 * P.lam - Ef P * (1 - 1) * P.lam ≠ 0 := by
    rw [e2]; exact (mul_pos hσ hZ1).ne'
  unfold CScontrol CSdiscl Ud Uw
  rw [WH_eq P γ hμ.ne' hZ.ne', WN_eq P γ hμ.ne' hσ.ne' hE.ne' hZ.ne' hX.ne',
    WL_eq P γ hμ.ne' hσ.ne' hE.ne' hX.ne' hY.ne', WH_eq P 1 hμ.ne' hZ1',
    WL_eq P 1 hμ.ne' hσ.ne' hE.ne' hX1' hY.ne', e1, e2]
  have hZ1n := hZ1.ne'
  have hXn := hX.ne'
  have hYn := hY.ne'
  have hZn := hZ.ne'
  have hσn := hσ.ne'
  generalize hXd : P.σ * P.mu - P.σ * P.α * γ * P.lam - Ef P * (1 - γ) * P.lam = X at hXn ⊢
  generalize hYd : P.σ * P.mu - Ef P * P.lam = Y at hYn ⊢
  generalize hZd : P.mu - P.α * γ * P.lam = Z at hZn ⊢
  generalize hZ1d : P.mu - P.α * P.lam = Z1 at hZ1n ⊢
  field_simp
  subst hXd hYd hZd hZ1d
  unfold Ef
  ring

/-- With `α = 1` withholding is strictly worse, so no equilibrium has `γ* < 1`. -/
lemma alpha_one (P : Params) (hS : P.Standing) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hα : P.α = 1) : Uw P γ < Ud P γ := by
  obtain ⟨hE, hY, hZ1, hZ, hX⟩ := facts P hS γ hγ0 hγ1
  obtain ⟨hμ, hσ, _, _, _, hl, _, hc, _⟩ := hS
  have key : WN P γ - WH P γ = P.lam * P.σ /
      ((P.σ * P.mu - P.σ * P.α * γ * P.lam - Ef P * (1 - γ) * P.lam) *
        (P.mu - P.α * γ * P.lam)) := by
    rw [WH_eq P γ hμ.ne' hZ.ne', WN_eq P γ hμ.ne' hσ.ne' hE.ne' hZ.ne' hX.ne']
    have hEσ : Ef P = P.σ := by unfold Ef; rw [hα]; ring
    have hXn := hX.ne'
    have hZn := hZ.ne'
    have hσn := hσ.ne'
    rw [hEσ] at hXn ⊢
    rw [hα] at hXn hZn ⊢
    generalize hXd : P.σ * P.mu - P.σ * 1 * γ * P.lam - P.σ * (1 - γ) * P.lam = X at hXn ⊢
    generalize hZd : P.mu - 1 * γ * P.lam = Z at hZn ⊢
    field_simp
    ring
  have hpos : 0 < WN P γ - WH P γ := by
    rw [key]; exact div_pos (mul_pos hl hσ) (mul_pos hX hZ)
  unfold Ud Uw
  rw [hα]
  nlinarith [mul_pos hc hpos]

end PQSolAda

-- Theorem 1, p. 15: customer control compared with compulsory disclosure.
open PrivacyQueue.Control in
theorem solution (P : Params) (hS : P.Standing) (γs : ℝ)
    (hEq : IsEquilibrium P γs) :
    (P.σ < 1 → CScontrol P γs ≤ CSdiscl P ∧
      (γs < 1 → 0 < P.α → CScontrol P γs < CSdiscl P)) ∧
    (1 < P.σ → CSdiscl P ≤ CScontrol P γs ∧
      (γs < 1 → 0 < P.α → CSdiscl P < CScontrol P γs)) := by
  have hγ : 0 ≤ γs ∧ γs ≤ 1 := by
    rcases hEq with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h0, h1, _⟩
    · rw [h]; norm_num
    · rw [h]; norm_num
    · exact ⟨h0.le, h1.le⟩
  obtain ⟨hγ0, hγ1⟩ := hγ
  obtain ⟨hE, hY, hZ1, hZ, hX⟩ := PQSolAda.facts P hS γs hγ0 hγ1
  have hd := PQSolAda.diff_eq P hS γs hγ0 hγ1
  obtain ⟨hμ, hσ, _, hα0, hα1, hl, _, hc, _⟩ := hS
  have hM : 0 < P.mu - P.α * P.lam + P.α * P.lam * P.σ := by
    have := mul_nonneg (mul_nonneg hα0 hl.le) hσ.le
    linarith
  have hden : 0 < P.σ * (P.mu - P.α * γs * P.lam) *
      (P.σ * P.mu - P.σ * P.α * γs * P.lam - PQSolAda.Ef P * (1 - γs) * P.lam) *
      (P.mu - P.α * P.lam) := mul_pos (mul_pos (mul_pos hσ hZ) hX) hZ1
  have hK : 0 ≤ P.c * (1 - γs) ^ 2 * P.α * (1 - P.α) * P.lam ^ 2 *
      (P.mu - P.α * P.lam + P.α * P.lam * P.σ) /
      (P.σ * (P.mu - P.α * γs * P.lam) *
        (P.σ * P.mu - P.σ * P.α * γs * P.lam - PQSolAda.Ef P * (1 - γs) * P.lam) *
        (P.mu - P.α * P.lam)) := by
    apply div_nonneg _ hden.le
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc.le (sq_nonneg _)) hα0)
      (sub_nonneg.2 hα1)) (sq_nonneg _)) hM.le
  have hstrict : γs < 1 → 0 < P.α →
      0 < P.c * (1 - γs) ^ 2 * P.α * (1 - P.α) * P.lam ^ 2 *
        (P.mu - P.α * P.lam + P.α * P.lam * P.σ) /
        (P.σ * (P.mu - P.α * γs * P.lam) *
          (P.σ * P.mu - P.σ * P.α * γs * P.lam - PQSolAda.Ef P * (1 - γs) * P.lam) *
          (P.mu - P.α * P.lam)) := by
    intro hg hα
    have hα1' : P.α < 1 := by
      rcases lt_or_eq_of_le hα1 with h | h
      · exact h
      · exfalso
        have hS' : P.Standing := ⟨hμ, hσ, by assumption, hα0, hα1, hl, by assumption, hc,
          by assumption⟩
        rcases hEq with ⟨h0, hlt⟩ | ⟨h1, _⟩ | ⟨_, _, heq, _⟩
        · have := PQSolAda.alpha_one P hS' 0 le_rfl zero_le_one h
          linarith
        · linarith
        · have := PQSolAda.alpha_one P hS' γs hγ0 hγ1 h
          linarith
    apply div_pos _ hden
    have h1 : 0 < 1 - P.α := by linarith
    have h2 : 0 < (1 - γs) ^ 2 := pow_pos (by linarith) 2
    have := mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hc h2) hα) h1) (pow_pos hl 2)) hM
    exact this
  refine ⟨fun hs => ⟨?_, fun hg hα => ?_⟩, fun hs => ⟨?_, fun hg hα => ?_⟩⟩
  · nlinarith
  · have := hstrict hg hα; nlinarith
  · nlinarith
  · have := hstrict hg hα; nlinarith
