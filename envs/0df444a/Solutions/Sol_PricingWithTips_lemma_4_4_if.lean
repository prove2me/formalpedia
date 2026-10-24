-- Prove2me | solution 1 for PricingWithTips.lemma_4_4_if
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T23:24:44.303219+00:00
-- url     : https://prove2.me/submissions/d6c28894-7435-4bf9-9fba-56a424b4ea91

import Theorems.Thm_PricingWithTips_buyerMatching_prices_of_maximum
import Theorems.Thm_PricingWithTips_minimumTip_eq_requiredTip_off_order_of_plan

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

private theorem minimumTip_zero_of_trade
    (M : Market B S D) (A : Allocation B S D) (w : B → S → ℝ)
    (hplan : IsCourierPlanFor M A w) {b : B} {s : S} {d : D}
    (ht : A.Trades b s d) : minimumTip M w (fun _ _ => 0) b s = 0 := by
  classical
  let T : Set ℝ := {τ | 0 ≤ τ ∧ ∃ d, CourierAccepts M w (fun _ _ => 0) b s τ d}
  have haccept : CourierAccepts M w (fun _ _ => 0) b s 0 d := by
    constructor
    · simpa using (hplan.2.1 d b s ht).1
    · intro b' s'
      simpa [counterfactualTip] using (hplan.2.1 d b s ht).2 b' s'
  have hzero : (0 : ℝ) ∈ T := ⟨le_refl _, d, haccept⟩
  change sInf T = 0
  apply le_antisymm
  · exact csInf_le ⟨0, fun τ hτ => hτ.1⟩ hzero
  · exact le_csInf ⟨0, hzero⟩ (fun τ hτ => hτ.1)

theorem solution [Nonempty D]
    (M : Market B S D) (A : Allocation B S D) (uBar : D → ℝ)
    (hu : IsMaximalCourierUtility M A uBar)
    (hmax : IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar)) :
    HasWithTipEquilibriumAt M A := by
  classical
  obtain ⟨w, hplan, hreal⟩ := hu.1
  obtain ⟨p, hp, hbuyer, hunsold⟩ :=
    buyerMatching_prices_of_maximum A.toBuyerMatching (adjustedValue M A uBar) hmax
  have hminreq : ∀ b s, minimumTip M w (fun _ _ => 0) b s =
      requiredTip M A uBar b s := by
    intro b s
    by_cases hd : A.Delivers b s
    · obtain ⟨d, ht⟩ := hd
      rw [minimumTip_zero_of_trade M A w hplan ht]
      have hd' : A.Delivers b s := ⟨d, ht⟩
      simp [requiredTip, hd']
    · exact minimumTip_eq_requiredTip_off_order_of_plan M A w uBar hplan hreal b s hd
  refine ⟨p, w, (fun _ _ => 0), hp, hplan.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b s
    exact le_refl _
  · intro b
    have hb := hbuyer b
    cases ha : A.assigned b with
    | none =>
        simp only [Allocation.toBuyerMatching, ha, Option.map_none] at hb
        simp only [ha]
        intro s
        have hs := hb s
        rw [hminreq b s]
        dsimp [adjustedValue] at hs
        linarith
    | some sd =>
        cases sd with
        | mk s₀ d₀ =>
            simp only [Allocation.toBuyerMatching, ha, Option.map_some] at hb
            simp only [ha]
            have ht : A.Trades b s₀ d₀ := ha
            have hreq0 : requiredTip M A uBar b s₀ = 0 := by
              have hd : A.Delivers b s₀ := ⟨d₀, ht⟩
              simp [requiredTip, hd]
            constructor
            · rw [hminreq, hreq0]
            · constructor
              · have h0 := hb.1
                rw [hminreq, hreq0]
                dsimp [adjustedValue] at h0
                linarith
              · intro s'
                have hs := hb.2 s'
                rw [hminreq b s', hminreq b s₀]
                dsimp [adjustedValue] at hs
                linarith
  · intro d b s ht
    have hc := hplan.2.1 d b s ht
    simpa [courierUtility] using hc
  · intro d hnot b s
    have hc := hplan.2.2.1 d hnot b s
    simpa [courierUtility] using hc
  · intro s hs
    apply hunsold s
    rintro ⟨b, hb⟩
    change (A.assigned b).map Prod.fst = some s at hb
    obtain ⟨sd, hsd, hf⟩ := Option.map_eq_some_iff.mp hb
    cases sd with
    | mk s' d =>
        dsimp at hf
        subst s'
        exact hs ⟨b, d, hsd⟩
  · intro b s hd
    exact ⟨hplan.2.2.2 b s hd, rfl⟩
