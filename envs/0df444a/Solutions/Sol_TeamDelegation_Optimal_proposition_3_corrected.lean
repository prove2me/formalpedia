-- Prove2me | solution 1 for TeamDelegation.Optimal.proposition_3_corrected
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T13:52:31.349248+00:00
-- url     : https://prove2.me/submissions/f3922038-357e-446d-a925-345232b44656

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model

open TeamDelegation.Optimal

/-- The punishment (γ₁, shirk, shirk), used in both states. -/
private noncomputable def punσ : Mixed ActA ActB :=
  ⟨fun a => if a = ((0 : Method), false) then 1 else 0, fun b => if b = false then 1 else 0⟩

private lemma nonneg_of_mul_pos_eq {X Y D : ℝ} (h : X * D = Y) (hY : 0 ≤ Y) (hD : 0 < D) :
    0 ≤ X := by
  by_contra hX
  push Not at hX
  have : X * D < 0 := mul_neg_of_neg_of_pos hX hD
  linarith

/-- Implementation from the scalar inequalities on the two bonuses. -/
private lemma implements_of (P : Params) (c1A c1B ΔA ΔB w v : ℝ)
    (hδ0 : 0 < P.δ) (hδ1 : P.δ < 1) (hr0 : 0 ≤ P.r) (hr1 : P.r < 1)
    (h01 : P.p0 < P.p1) (h12 : P.p1 < P.p2) (hq01 : P.q0 < P.q1) (hq12 : P.q1 < P.q2)
    (hqp0 : P.q0 < P.p0) (hqp1 : P.q1 < P.p1) (hqp2 : P.q2 < P.p2)
    (hc1 : P.p1 - P.p0 < P.p2 - P.p1) (hc3 : P.q2 - P.q1 < P.p2 - P.p1)
    (hc4 : P.q1 - P.q0 < P.p1 - P.p0)
    (hΔ : 0 < ΔA) (hw0 : 0 ≤ w) (hv0 : 0 ≤ v)
    (hWb : w * (P.p2 - P.p1) ≤ P.e) (hVb : v * (P.p2 - P.p1) ≤ P.e)
    (hN5 : (P.p0 - P.q0) * w ≤ ΔA)
    (hD0a : w * (P.p2 - (1 - P.δ) * P.p1 - P.δ * (P.r * P.p0 + (1 - P.r) * P.q0)) ≥
      P.e + P.δ * (1 - P.r) * ΔA)
    (hD1d : w * (P.p2 - (1 - P.δ) * P.q1 - P.δ * (P.r * P.p0 + (1 - P.r) * P.q0)) ≥
      P.e + (1 - P.δ * P.r) * ΔA)
    (hvB : v * (P.p2 - (1 - P.δ) * P.p1 - P.δ * (P.r * P.p0 + (1 - P.r) * P.q0)) ≥
      P.e + P.δ * (1 - P.r) * ΔB) :
    Implements P (Costs.ofDeltas c1A c1B ΔA ΔB) .deleg w v := by
  have he : 0 ≤ P.e := le_trans (mul_nonneg hw0 (by linarith)) hWb
  have hN1 : (P.p1 - P.p0) * w ≤ P.e := by
    have := mul_le_mul_of_nonneg_left hc1.le hw0; nlinarith
  have hN1B : (P.p1 - P.p0) * v ≤ P.e := by
    have := mul_le_mul_of_nonneg_left hc1.le hv0; nlinarith
  have hpq0w := mul_nonneg (sub_pos.2 hqp0).le hw0
  have hpq1w := mul_nonneg (sub_pos.2 hqp1).le hw0
  have hpq2w := mul_nonneg (sub_pos.2 hqp2).le hw0
  have h4w := mul_nonneg (sub_pos.2 hc4).le hw0
  have h4v := mul_nonneg (sub_pos.2 hc4).le hv0
  have hδ' : 0 ≤ 1 - P.δ := by linarith
  -- G = cont - pun ≥ 0
  have hG : 0 ≤ (P.p2 - (P.r * P.p0 + (1 - P.r) * P.q0)) * w - P.e - (1 - P.r) * ΔA := by
    have k1 := mul_nonneg hδ' (sub_nonneg.2 hWb)
    have hδG : 0 ≤ P.δ * ((P.p2 - (P.r * P.p0 + (1 - P.r) * P.q0)) * w - P.e -
        (1 - P.r) * ΔA) := by nlinarith
    exact nonneg_of_mul_nonneg_right (by linarith [hδG]) hδ0
  have a := mul_nonneg hδ0.le hG
  have b := mul_nonneg hδ' (add_nonneg hpq2w hΔ.le)
  have c := mul_nonneg hδ' (add_nonneg hpq1w hΔ.le)
  have hq21w : (P.q2 - P.q1) * w ≤ P.e := by
    have := mul_le_mul_of_nonneg_left hc3.le hw0; nlinarith
  have d := mul_nonneg hδ' (sub_nonneg.2 hq21w)
  refine ⟨hw0, hv0, fun _ => punσ, ?_, ?_⟩
  · intro k
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro a; simp only [punσ]; split_ifs <;> norm_num
    · intro b; simp only [punσ]; split_ifs <;> norm_num
    · simp [punσ]
    · simp [punσ]
    · intro a ha; exact absurd trivial ha
    · intro b hb; exact absurd trivial hb
    · rintro ⟨m, x⟩ _
      fin_cases k <;> fin_cases m <;> cases x <;>
        simp [punσ, FiniteGame.expPayA, stageGame, payA, succProb, workers,
          Fintype.sum_prod_type, Costs.ofDeltas] <;> linarith
    · intro b _
      fin_cases k <;> cases b <;>
        simp [punσ, FiniteGame.expPayB, stageGame, payB, succProb, workers,
          Fintype.sum_prod_type, Costs.ofDeltas] <;> linarith
  · intro k
    constructor
    · rintro ⟨m, x⟩ _
      fin_cases k <;> fin_cases m <;> cases x <;>
        simp [punσ, punValueA, contValueA, FiniteGame.expPayA, stageGame, payA,
          succProb, workers, desiredA, Fintype.sum_prod_type, Costs.ofDeltas] <;>
        linarith
    · fin_cases k <;>
        simp [punσ, punValueB, contValueB, FiniteGame.expPayB, stageGame, payB,
          succProb, workers, desiredA, Fintype.sum_prod_type, Costs.ofDeltas] <;>
        linarith

set_option maxHeartbeats 1000000 in
theorem solution (P : Params) (hS : P.Standing)
    (hA1 : P.Assumption1) (c1A c1B ΔA ΔB : ℝ)
    (hAlo : DeltaHatA P < ΔA) (hAhi : ΔA < DeltaMaxA P)
    (hBhi : ΔB < DeltaMaxB P) (hBnonneg : 0 ≤ wdelB P ΔB) :
    Implements P (Costs.ofDeltas c1A c1B ΔA ΔB) .deleg
      (wdelA P ΔA) (wdelB P ΔB) := by
  obtain ⟨he, hδ0, hδ1, hr0, hr1, hq0, hp2⟩ := hS
  obtain ⟨h01, h12, hq01, hq12, hqp0, hqp1, hqp2, hc1, hc2, hc3, hc4⟩ := hA1
  have hpmdef : punishmentMean P = P.r * P.p0 + (1 - P.r) * P.q0 := rfl
  have h1r : 0 < 1 - P.r := by linarith
  have hu : 0 < P.δ * (1 - P.r) := mul_pos hδ0 h1r
  have h1dr : 0 < 1 - P.δ * P.r := by nlinarith
  have hδ' : 0 < 1 - P.δ := by linarith
  -- denominators
  obtain ⟨pm, hpm⟩ : ∃ x, x = P.r * P.p0 + (1 - P.r) * P.q0 := ⟨_, rfl⟩
  have hpm0 : pm - P.p0 = -((1 - P.r) * (P.p0 - P.q0)) := by rw [hpm]; ring
  have hpmq : P.q0 ≤ pm := by
    have := mul_nonneg hr0 (sub_pos.2 hqp0).le; rw [hpm]; nlinarith
  have hpmp : pm ≤ P.p0 := by
    have := mul_nonneg h1r.le (sub_pos.2 hqp0).le; linarith
  have hDc : 0 < P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0 := by
    have : P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0 =
        (P.p2 - P.p1) + P.δ * (P.p1 - P.p0) := by ring
    rw [this]; have := mul_pos hδ0 (sub_pos.2 h01); linarith
  obtain ⟨Dd, hDd⟩ : ∃ x, x = P.p2 - (1 - P.δ) * P.p1 - P.δ * pm := ⟨_, rfl⟩
  obtain ⟨D2, hD2⟩ : ∃ x, x = P.p2 - (1 - P.δ) * P.q1 - P.δ * pm := ⟨_, rfl⟩
  obtain ⟨dc, hdc⟩ : ∃ x, x = P.p2 - P.p1 * (1 - P.δ * P.r) + P.q1 * P.δ * (1 - P.r) -
      P.δ * pm := ⟨_, rfl⟩
  have hDdpos : 0 < Dd := by
    have : Dd = (P.p2 - P.p1) + P.δ * (P.p1 - pm) := by rw [hDd]; ring
    rw [this]; have := mul_pos hδ0 (by linarith : (0:ℝ) < P.p1 - pm); linarith
  have hD2eq : D2 = Dd + (1 - P.δ) * (P.p1 - P.q1) := by rw [hD2, hDd]; ring
  have hD2pos : 0 < D2 := by
    rw [hD2eq]; have := mul_pos hδ' (sub_pos.2 hqp1); linarith
  have hdceq : dc = Dd - P.δ * (1 - P.r) * (P.p1 - P.q1) := by
    rw [hdc, hDd, hpm]; ring
  have hdcpos : 0 < dc := by
    have : dc = (P.p2 - P.p1) + P.δ * (P.r * (P.p1 - P.p0) + (1 - P.r) * (P.q1 - P.q0)) := by
      rw [hdc, hpm]; ring
    rw [this]
    have := mul_nonneg hr0 (sub_pos.2 h01).le
    have := mul_pos h1r (sub_pos.2 hq01)
    have := mul_pos hδ0 (by linarith : (0:ℝ) < P.r * (P.p1 - P.p0) + (1 - P.r) * (P.q1 - P.q0))
    linarith
  -- thresholds
  have hHat : P.e * (P.p0 - P.q0) < ΔA * (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0) := by
    unfold DeltaHatA at hAlo; rwa [div_lt_iff₀ hDc] at hAlo
  have hΔpos : 0 < ΔA := by
    have := mul_pos he (sub_pos.2 hqp0)
    by_contra h; push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hDc.le; linarith
  have hMaxA : ΔA * ((1 - P.δ * P.r) * (P.p2 - P.p1)) < P.e * (D2 - (P.p2 - P.p1)) := by
    unfold DeltaMaxA at hAhi
    rw [lt_div_iff₀ (mul_pos h1dr (sub_pos.2 h12))] at hAhi
    rw [hD2, hpm]; rw [← hpmdef]; linarith
  have hMaxB : ΔB * ((1 - P.r) * (P.p2 - P.p1)) < P.e * (P.p1 - pm) := by
    unfold DeltaMaxB at hBhi
    rw [lt_div_iff₀ (mul_pos h1r (sub_pos.2 h12))] at hBhi
    rw [hpm, ← hpmdef]; linarith
  have hcrit : DeltaCritA P = (P.p1 - P.q1) * P.e / dc := by
    unfold DeltaCritA; rw [hdc, hpm, hpmdef]
  -- the B bonus
  have hv : wdelB P ΔB * Dd = P.e + P.δ * (1 - P.r) * ΔB := by
    unfold wdelB; rw [hpmdef, ← hpm, ← hDd, div_mul_cancel₀ _ hDdpos.ne']
  have hVb : wdelB P ΔB * (P.p2 - P.p1) ≤ P.e := by
    have key : (P.e - wdelB P ΔB * (P.p2 - P.p1)) * Dd =
        P.δ * (P.e * (P.p1 - pm) - ΔB * ((1 - P.r) * (P.p2 - P.p1))) := by
      have : (P.e - wdelB P ΔB * (P.p2 - P.p1)) * Dd =
          P.e * Dd - (wdelB P ΔB * Dd) * (P.p2 - P.p1) := by ring
      rw [this, hv, hDd]; ring
    have := nonneg_of_mul_pos_eq key (mul_nonneg hδ0.le (by linarith)) hDdpos
    linarith
  -- the A bonus, by branch
  obtain ⟨w, hw⟩ : ∃ x, x = wdelA P ΔA := ⟨_, rfl⟩
  have hfacts : 0 ≤ w ∧ w * (P.p2 - P.p1) ≤ P.e ∧ (P.p0 - P.q0) * w ≤ ΔA ∧
      w * Dd ≥ P.e + P.δ * (1 - P.r) * ΔA ∧ w * D2 ≥ P.e + (1 - P.δ * P.r) * ΔA := by
    by_cases hb : ΔA ≤ DeltaCritA P
    · have hw1 : w * Dd = P.e + P.δ * (1 - P.r) * ΔA := by
        rw [hw]; unfold wdelA; rw [if_pos hb, hpmdef, ← hpm, ← hDd,
          div_mul_cancel₀ _ hDdpos.ne']
      have hb' : ΔA * dc ≤ (P.p1 - P.q1) * P.e := by
        rw [hcrit, le_div_iff₀ hdcpos] at hb; exact hb
      refine ⟨?_, ?_, ?_, hw1.ge, ?_⟩
      · exact nonneg_of_mul_pos_eq hw1 (by have := mul_pos hu hΔpos; linarith) hDdpos
      · -- Δ(1-r)(p2-p1) < e(p1-pm)
        have k1 : ΔA * ((1 - P.r) * (P.p2 - P.p1)) * dc ≤
            (P.p1 - P.q1) * P.e * ((1 - P.r) * (P.p2 - P.p1)) := by
          have := mul_le_mul_of_nonneg_right hb' (mul_pos h1r (sub_pos.2 h12)).le
          linarith
        have k2 : (P.p1 - P.q1) * P.e * ((1 - P.r) * (P.p2 - P.p1)) <
            P.e * (P.p1 - pm) * dc := by
          have hdc' : dc = (P.p2 - P.p1) + P.δ * (P.r * (P.p1 - P.p0) +
              (1 - P.r) * (P.q1 - P.q0)) := by rw [hdc, hpm]; ring
          have e1 : P.p1 - pm = P.r * (P.p1 - P.p0) + (1 - P.r) * (P.p1 - P.q0) := by
            rw [hpm]; ring
          rw [e1, hdc']
          have := mul_pos (mul_pos he h1r) (mul_pos (sub_pos.2 hq01) (sub_pos.2 h12))
          have := mul_nonneg (mul_nonneg he.le hr0)
            (mul_nonneg (sub_pos.2 h01).le (sub_pos.2 h12).le)
          have : 0 ≤ P.e * (P.r * (P.p1 - P.p0) + (1 - P.r) * (P.p1 - P.q0)) *
              (P.δ * (P.r * (P.p1 - P.p0) + (1 - P.r) * (P.q1 - P.q0))) := by
            apply mul_nonneg (mul_nonneg he.le _) (mul_nonneg hδ0.le _)
            · have := mul_nonneg hr0 (sub_pos.2 h01).le
              have := mul_nonneg h1r.le (by linarith : (0:ℝ) ≤ P.p1 - P.q0); linarith
            · have := mul_nonneg hr0 (sub_pos.2 h01).le
              have := mul_nonneg h1r.le (sub_pos.2 hq01).le; linarith
          linarith
        have k3 : ΔA * ((1 - P.r) * (P.p2 - P.p1)) < P.e * (P.p1 - pm) := by
          by_contra h; push Not at h
          have := mul_le_mul_of_nonneg_right h hdcpos.le; linarith
        have key : (P.e - w * (P.p2 - P.p1)) * Dd =
            P.δ * (P.e * (P.p1 - pm) - ΔA * ((1 - P.r) * (P.p2 - P.p1))) := by
          have : (P.e - w * (P.p2 - P.p1)) * Dd = P.e * Dd - (w * Dd) * (P.p2 - P.p1) := by
            ring
          rw [this, hw1, hDd]; ring
        have := nonneg_of_mul_pos_eq key (mul_nonneg hδ0.le (by linarith)) hDdpos
        linarith
      · have key : (ΔA - (P.p0 - P.q0) * w) * Dd =
            ΔA * (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0) - P.e * (P.p0 - P.q0) := by
          have : (ΔA - (P.p0 - P.q0) * w) * Dd = ΔA * Dd - (P.p0 - P.q0) * (w * Dd) := by
            ring
          rw [this, hw1, hDd, hpm]; ring
        have := nonneg_of_mul_pos_eq key (by linarith) hDdpos
        linarith
      · have key : (w * D2 - (P.e + (1 - P.δ * P.r) * ΔA)) * Dd =
            (1 - P.δ) * ((P.p1 - P.q1) * P.e - ΔA * dc) := by
          have : (w * D2 - (P.e + (1 - P.δ * P.r) * ΔA)) * Dd =
              (w * Dd) * D2 - (P.e + (1 - P.δ * P.r) * ΔA) * Dd := by ring
          rw [this, hw1, hdceq, hD2eq]; ring
        have := nonneg_of_mul_pos_eq key (mul_nonneg hδ'.le (by linarith)) hDdpos
        linarith
    · push Not at hb
      have hw2 : w * D2 = P.e + (1 - P.δ * P.r) * ΔA := by
        rw [hw]; unfold wdelA; rw [if_neg (not_le.2 hb), hpmdef, ← hpm, ← hD2,
          div_mul_cancel₀ _ hD2pos.ne']
      have hb' : (P.p1 - P.q1) * P.e < ΔA * dc := by
        rw [hcrit, div_lt_iff₀ hdcpos] at hb; exact hb
      have hcritpos : 0 < DeltaCritA P := by
        rw [hcrit]; exact div_pos (mul_pos (sub_pos.2 hqp1) he) hdcpos
      refine ⟨?_, ?_, ?_, ?_, hw2.ge⟩
      · exact nonneg_of_mul_pos_eq hw2 (by have := mul_pos h1dr hΔpos; linarith) hD2pos
      · have key : (P.e - w * (P.p2 - P.p1)) * D2 =
            P.e * (D2 - (P.p2 - P.p1)) - ΔA * ((1 - P.δ * P.r) * (P.p2 - P.p1)) := by
          have : (P.e - w * (P.p2 - P.p1)) * D2 = P.e * D2 - (w * D2) * (P.p2 - P.p1) := by
            ring
          rw [this, hw2]; ring
        have := nonneg_of_mul_pos_eq key (by linarith) hD2pos
        linarith
      · -- slope s2 ≥ Dc and Δ > crit > hat
        have hs2 : ΔA * (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0) ≤
            ΔA * ((P.p2 - P.p0) - (1 - P.δ) * (P.q1 - P.q0)) := by
          apply mul_le_mul_of_nonneg_left _ hΔpos.le
          have := mul_le_mul_of_nonneg_left hc4.le hδ'.le
          linarith
        have key : (ΔA - (P.p0 - P.q0) * w) * D2 =
            ΔA * ((P.p2 - P.p0) - (1 - P.δ) * (P.q1 - P.q0)) - P.e * (P.p0 - P.q0) := by
          have : (ΔA - (P.p0 - P.q0) * w) * D2 = ΔA * D2 - (P.p0 - P.q0) * (w * D2) := by
            ring
          rw [this, hw2, hD2, hpm]; ring
        have := nonneg_of_mul_pos_eq key (by linarith) hD2pos
        linarith
      · have key : (w * Dd - (P.e + P.δ * (1 - P.r) * ΔA)) * D2 =
            (1 - P.δ) * (ΔA * dc - (P.p1 - P.q1) * P.e) := by
          have : (w * Dd - (P.e + P.δ * (1 - P.r) * ΔA)) * D2 =
              (w * D2) * Dd - (P.e + P.δ * (1 - P.r) * ΔA) * D2 := by ring
          rw [this, hw2, hdceq, hD2eq]; ring
        have := nonneg_of_mul_pos_eq key (mul_nonneg hδ'.le (by linarith)) hD2pos
        linarith
  obtain ⟨hw0, hWb, hN5, hD0a, hD1d⟩ := hfacts
  rw [← hw]
  rw [hDd, hpm] at hD0a hv
  rw [hD2, hpm] at hD1d
  exact implements_of P c1A c1B ΔA ΔB w (wdelB P ΔB) hδ0 hδ1 hr0 hr1 h01 h12 hq01 hq12
    hqp0 hqp1 hqp2 hc1 hc3 hc4 hΔpos hw0 hBnonneg hWb hVb hN5 hD0a hD1d hv.ge
