-- Prove2me | solution 2 for PricingWithTips.equilibrium_has_adjusted_prices
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T22:52:40.360983+00:00
-- url     : https://prove2.me/submissions/2bc6f12b-9041-4b9e-8986-38c667424976

import Theorems.Thm_PricingWithTips_minimumTip_le_requiredTip_off_order_with_tips

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

private theorem plan_realized_bounds
    (M : Market B S D) (A : Allocation B S D) (w : B → S → ℝ)
    (hplan : IsCourierPlanFor M A w) :
    (∀ d, 0 ≤ courierRealizedUtility M A w d) ∧
    (∀ d b s, w b s - M.cost d b s ≤ courierRealizedUtility M A w d) := by
  classical
  constructor
  · intro d
    by_cases h : ∃ b s, A.Trades b s d
    · let b₀ := Classical.choose h
      let hs := Classical.choose_spec h
      let s₀ := Classical.choose hs
      have ht : A.Trades b₀ s₀ d := Classical.choose_spec hs
      simpa only [courierRealizedUtility, dif_pos h] using
        (hplan.2.1 d b₀ s₀ ht).1
    · simp [courierRealizedUtility, h]
  · intro d b s
    by_cases h : ∃ b' s', A.Trades b' s' d
    · let b₀ := Classical.choose h
      let hs := Classical.choose_spec h
      let s₀ := Classical.choose hs
      have ht : A.Trades b₀ s₀ d := Classical.choose_spec hs
      simpa only [courierRealizedUtility, dif_pos h] using
        (hplan.2.1 d b₀ s₀ ht).2 b s
    · have hnot : ¬ A.CourierWorks d := h
      simpa [courierRealizedUtility, h] using hplan.2.2.1 d hnot b s

theorem solution [Nonempty D]
    (M : Market B S D) (A : Allocation B S D) (uBar : D → ℝ)
    (hu : IsMaximalCourierUtility M A uBar)
    (heq : HasWithTipEquilibriumAt M A) :
    ∃ p : S → ℝ,
      (∀ s, 0 ≤ p s) ∧
      (∀ b,
        match A.toBuyerMatching.assigned b with
        | none => ∀ s, adjustedValue M A uBar b s - p s ≤ 0
        | some s =>
            0 ≤ adjustedValue M A uBar b s - p s ∧
              ∀ s', adjustedValue M A uBar b s' - p s' ≤
                adjustedValue M A uBar b s - p s) ∧
      (∀ s, (¬ ∃ b, A.toBuyerMatching.assigned b = some s) → p s = 0) := by
  classical
  obtain ⟨p, w, t, heq₀⟩ := heq
  rcases heq₀ with ⟨hp, hw, ht, hbuyer, hcourier, hidle, hunsold, hunpaid⟩
  let wplus : B → S → ℝ := fun b s => w b s + t b s
  have hplan : IsCourierPlanFor M A wplus := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b s
      dsimp [wplus]
      linarith [hw b s, ht b s]
    · intro d b s ht
      simpa [courierUtility, wplus] using hcourier d b s ht
    · intro d hd b s
      simpa [courierUtility, wplus] using hidle d hd b s
    · intro b s hd
      have hzero := hunpaid b s hd
      simp [wplus, hzero.1, hzero.2]
  have hbounds := plan_realized_bounds M A wplus hplan
  have hbar_nonneg : ∀ d, 0 ≤ uBar d := by
    intro d
    exact le_trans (hbounds.1 d) (hu.2 wplus hplan d)
  have hupper : ∀ d b s, w b s + t b s - M.cost d b s ≤ uBar d := by
    intro d b s
    exact le_trans (hbounds.2 d b s) (hu.2 wplus hplan d)
  refine ⟨p, hp, ?_, ?_⟩
  · intro b
    cases h : A.assigned b with
    | none =>
        simp only [Allocation.toBuyerMatching, h, Option.map_none]
        intro s
        have hoff : ¬ A.Delivers b s := by
          rintro ⟨d, ht⟩
          change A.assigned b = some (s, d) at ht
          simp [h] at ht
        have hwzero := (hunpaid b s hoff).1
        have htip := minimumTip_le_requiredTip_off_order_with_tips
          M A w t uBar b s hoff hwzero ht hbar_nonneg hupper
        have hb := hbuyer b
        simp only [h] at hb
        dsimp [adjustedValue]
        linarith [hb s]
    | some sd =>
        rcases sd with ⟨s₀, d₀⟩
        simp only [Allocation.toBuyerMatching, h, Option.map_some]
        have hb := hbuyer b
        simp only [h] at hb
        have htrade : A.Trades b s₀ d₀ := h
        have hdel : A.Delivers b s₀ := ⟨d₀, htrade⟩
        have hreq : requiredTip M A uBar b s₀ = 0 := by
          simp [requiredTip, hdel]
        have htip₀ : t b s₀ = minimumTip M w t b s₀ := hb.1
        constructor
        · dsimp [adjustedValue]
          rw [hreq]
          linarith [hb.2.1, ht b s₀]
        · intro s'
          by_cases hs : s' = s₀
          · subst s'
            exact le_refl _
          · have hoff : ¬ A.Delivers b s' := by
              rintro ⟨d, ht⟩
              change A.assigned b = some (s', d) at ht
              have hpairs := Option.some.inj (h.symm.trans ht)
              exact hs (congrArg Prod.fst hpairs).symm
            have hwzero := (hunpaid b s' hoff).1
            have htip := minimumTip_le_requiredTip_off_order_with_tips
              M A w t uBar b s' hoff hwzero ht hbar_nonneg hupper
            have hpref := hb.2.2 s'
            dsimp [adjustedValue]
            rw [hreq]
            linarith [ht b s₀]
  · intro s hs
    apply hunsold s
    rintro ⟨b, d, ht⟩
    apply hs
    refine ⟨b, ?_⟩
    change A.assigned b = some (s, d) at ht
    simp [Allocation.toBuyerMatching, ht]
