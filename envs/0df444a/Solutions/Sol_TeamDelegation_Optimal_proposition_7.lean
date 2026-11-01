-- Prove2me | solution 1 for TeamDelegation.Optimal.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T13:40:24.039531+00:00
-- url     : https://prove2.me/submissions/95d583bf-7e59-4fd4-862c-3b2604839e42

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model
import Theorems.Thm_TeamDelegation_Optimal_centralisation_optimum
import Theorems.Thm_TeamDelegation_Optimal_threshold_order
import Theorems.Thm_TeamDelegation_Optimal_proposition_3_corrected
import Theorems.Thm_TeamDelegation_Optimal_cost_comparison
import Theorems.Thm_TeamDelegation_Optimal_surplus_characterisation
import Theorems.Thm_TeamDelegation_Optimal_claim_1
import Theorems.Thm_TeamDelegation_Optimal_ordering_75_77
import Theorems.Thm_TeamDelegation_Optimal_surplus_implies_collusion_proof

open TeamDelegation.Optimal

private lemma aux60 (a d u D X e s : ℝ) (hD : 0 < D) (ha : 0 < a) (hdu : 0 < a * d * u)
    (hX : X = D - a) (hs : 2 * e * X / (a * d * u) < s) :
    a * ((2 * e + d * u * s) / D) ≥ 2 * e := by
  rw [div_lt_iff₀ hdu] at hs
  rw [ge_iff_le, mul_div_assoc', le_div_iff₀ hD]
  subst hX
  nlinarith

private lemma aux64 (k d u D e s : ℝ) (hD : 0 < D) (hden : 0 < D - k * d * u)
    (hs : s < k * (2 * e) / (D - k * d * u)) :
    k * ((2 * e + d * u * s) / D) ≥ s := by
  rw [lt_div_iff₀ hden] at hs
  rw [ge_iff_le, mul_div_assoc', le_div_iff₀ hD]
  nlinarith

private lemma aux66 (k d u D Y den e s : ℝ) (hD : 0 < D) (hden : 0 < den)
    (hdenEq : den = D - k * d * u) (hY : Y = k - D) (hs : s < 2 * e * Y / den) :
    k * ((2 * e + d * u * s) / D) ≥ 2 * e + s := by
  rw [lt_div_iff₀ hden] at hs
  rw [ge_iff_le, mul_div_assoc', le_div_iff₀ hD]
  subst hdenEq hY
  nlinarith

theorem solution (P : Params) (hS : P.Standing)
    (hA1 : P.Assumption1) (c1A c1B : ℝ) :
    ∃ ΔA ΔB : ℝ,
      DeltaHatA P < ΔA ∧ ΔA < DeltaMaxA P ∧ ΔB < DeltaMaxB P ∧
      Implements P (Costs.ofDeltas c1A c1B ΔA ΔB) .deleg
        (wdelA P ΔA) (wdelB P ΔB) ∧
      Implements P (Costs.ofDeltas c1A c1B ΔA ΔB) .cent
        (wcent P) (wcent P) ∧
      (∀ wA wB : ℝ,
        Implements P (Costs.ofDeltas c1A c1B ΔA ΔB) .cent wA wB →
          wageCost P (wdelA P ΔA) (wdelB P ΔB) < wageCost P wA wB) ∧
      CollusionProof P (Costs.ofDeltas c1A c1B ΔA ΔB) .deleg
        (wdelA P ΔA) (wdelB P ΔB) := by
  have hS' := hS
  have hA1' := hA1
  obtain ⟨he, hδ0, hδ1, hr0, hr1, hq0, hp2⟩ := hS
  obtain ⟨h01, h12, hq01, hq12, hqp0, hqp1, hqp2, hc1, hc2, hc3, hc4⟩ := hA1
  obtain ⟨hMA, hMB, hH, hHC, hCM⟩ := threshold_order P hS' hA1'
  obtain ⟨hT1, hT2, hT3, hS0, hSCB⟩ := ordering_75_77 P hS' hA1'
  have hpmdef : punishmentMean P = P.r * P.p0 + (1 - P.r) * P.q0 := rfl
  have hpm1 : punishmentMean P < P.p1 := by
    rw [hpmdef]; nlinarith
  have hDd : 0 < P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P := by nlinarith
  have hδr : 0 < P.δ * (1 - P.r) := mul_pos hδ0 (by linarith)
  have hStar : DeltaStarSum P = 2 * DeltaHatA P := by
    unfold DeltaStarSum DeltaHatA; ring
  -- choice of the aggregate difference
  obtain ⟨t, ht⟩ : ∃ t, t = max (DeltaTilde1 P) (DeltaHatA P) := ⟨_, rfl⟩
  have ht1 : DeltaTilde1 P ≤ t := ht ▸ le_max_left _ _
  have ht2 : DeltaHatA P ≤ t := ht ▸ le_max_right _ _
  have htS : t < DeltaStarSum P := ht ▸ max_lt hT1 (by linarith)
  obtain ⟨s, hs⟩ : ∃ s, s = (t + DeltaStarSum P) / 2 := ⟨_, rfl⟩
  have hs1 : DeltaTilde1 P < s := by rw [hs]; linarith
  have hsH : DeltaHatA P < s := by rw [hs]; linarith
  have hsS : s < DeltaStarSum P := by rw [hs]; linarith
  obtain ⟨c, hc⟩ : ∃ c, c = P.e / (P.δ * (1 - P.r)) := ⟨_, rfl⟩
  have hcpos : 0 < c := hc ▸ div_pos he hδr
  have hcm : P.δ * (1 - P.r) * c = P.e := by rw [hc, mul_div_cancel₀ _ hδr.ne']
  obtain ⟨ΔA, hΔA⟩ : ∃ x, x = min (DeltaCritA P) (s + c) := ⟨_, rfl⟩
  obtain ⟨ΔB, hΔB⟩ : ∃ x, x = s - ΔA := ⟨_, rfl⟩
  have hAC : ΔA ≤ DeltaCritA P := hΔA ▸ min_le_left _ _
  have hAsc : ΔA ≤ s + c := hΔA ▸ min_le_right _ _
  have hAH : DeltaHatA P < ΔA := hΔA ▸ lt_min hHC (by linarith)
  have hBM : ΔB < DeltaMaxB P := by
    rcases le_total (DeltaCritA P) (s + c) with h | h
    · have : ΔA = DeltaCritA P := hΔA ▸ min_eq_left h
      rw [hΔB, this]; linarith
    · have : ΔA = s + c := hΔA ▸ min_eq_right h
      rw [hΔB, this]; linarith
  have hsum : ΔA + ΔB = s := by rw [hΔB]; ring
  have hsum0 : 0 ≤ ΔA + ΔB := by rw [hsum]; linarith
  have hwB : 0 ≤ wdelB P ΔB := by
    unfold wdelB
    apply div_nonneg _ hDd.le
    have h1 : -c ≤ ΔB := by rw [hΔB]; linarith
    have h2 : P.δ * (1 - P.r) * (-c) ≤ P.δ * (1 - P.r) * ΔB :=
      mul_le_mul_of_nonneg_left h1 hδr.le
    linarith
  have hC : (Costs.ofDeltas c1A c1B ΔA ΔB).Standing := by
    show c1A ≤ c1A + ΔA; linarith
  obtain ⟨hcentImpl, hcentMin⟩ :=
    centralisation_optimum P (Costs.ofDeltas c1A c1B ΔA ΔB) hS' hA1' hC
  have hcost := (cost_comparison P hS' hA1' ΔA ΔB hAC).2 (by rw [hsum]; exact hsS)
  -- total delegated wage
  have hW : wdelA P ΔA + wdelB P ΔB =
      (2 * P.e + P.δ * (1 - P.r) * s) /
        (P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P) := by
    unfold wdelA wdelB
    rw [if_pos hAC, ← add_div, ← hsum]
    congr 1; ring
  -- surplus constraints via Claim 1
  have h60 : (P.p2 - P.p0) * (wdelA P ΔA + wdelB P ΔB) ≥ 2 * P.e := by
    rw [hW]
    refine aux60 (P.p2 - P.p0) P.δ (1 - P.r) _
      (P.p0 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P) _ _ hDd (by linarith)
      (by have := mul_pos (sub_pos.2 (lt_trans h01 h12)) hδr; rw [mul_assoc]; exact this)
      (by ring) ?_
    simpa [DeltaTilde1] using hs1
  have hden2 : 0 < P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P -
      (P.p2 - P.q2) * P.δ * (1 - P.r) := by
    have e2 : P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P -
        (P.p2 - P.q2) * P.δ * (1 - P.r) = (1 - P.δ) * (P.p2 - P.p1) +
        P.δ * P.r * (P.p2 - P.p0) + P.δ * (1 - P.r) * (P.q2 - P.q0) := by
      rw [hpmdef]; ring
    rw [e2]
    have a1 := mul_pos (sub_pos.2 hδ1) (sub_pos.2 h12)
    have a2 := mul_nonneg (mul_nonneg hδ0.le hr0) (sub_pos.2 (lt_trans h01 h12)).le
    have a3 := mul_pos hδr (sub_pos.2 (lt_trans hq01 hq12))
    linarith
  have h64 : (P.p2 - P.q2) * (wdelA P ΔA + wdelB P ΔB) ≥ ΔA + ΔB := by
    rw [hW, hsum]
    refine aux64 _ _ _ _ _ _ hDd hden2 ?_
    have k : s < DeltaTilde2 P := lt_trans hsS hT2
    simpa [DeltaTilde2] using k
  have hden3 : 0 < P.p2 - P.p2 * P.δ * (1 - P.r) - (1 - P.δ) * P.p1 -
      P.δ * P.r * P.p0 := by
    have e3 : P.p2 - P.p2 * P.δ * (1 - P.r) - (1 - P.δ) * P.p1 - P.δ * P.r * P.p0 =
        (1 - P.δ) * (P.p2 - P.p1) + P.δ * P.r * (P.p2 - P.p0) := by ring
    rw [e3]
    have a1 := mul_pos (sub_pos.2 hδ1) (sub_pos.2 h12)
    have a2 := mul_nonneg (mul_nonneg hδ0.le hr0) (sub_pos.2 (lt_trans h01 h12)).le
    linarith
  have h66 : (P.p2 - P.q0) * (wdelA P ΔA + wdelB P ΔB) ≥ 2 * P.e + (ΔA + ΔB) := by
    rw [hW, hsum]
    refine aux66 (P.p2 - P.q0) P.δ (1 - P.r) _
      ((1 - P.δ) * P.p1 + P.δ * punishmentMean P - P.q0) _ _ _ hDd hden3 ?_ (by ring) ?_
    · rw [hpmdef]; ring
    · have k : s < DeltaTilde3 P := lt_trans hsS hT3
      unfold DeltaTilde3 at k
      convert k using 3
  have hSC := claim_1 P hS' hA1' _ _ hsum0 h60 h64 h66
  have hSM := (surplus_characterisation P hS' hA1' c1A c1B ΔA ΔB _ _ hAC hsum0).2 hSC
  have hAM : ΔA < DeltaMaxA P := lt_of_le_of_lt hAC hCM
  refine ⟨ΔA, ΔB, hAH, hAM, hBM,
    proposition_3_corrected P hS' hA1' c1A c1B ΔA ΔB hAH hAM hBM hwB,
    hcentImpl, ?_, surplus_implies_collusion_proof P hS' _ _ _ hSM⟩
  intro wA wB hImpl
  obtain ⟨hA', hB'⟩ := hcentMin wA wB hImpl
  unfold wageCost
  have hp2 : 0 < P.p2 := by linarith
  apply mul_lt_mul_of_pos_left _ hp2
  linarith
