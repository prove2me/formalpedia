-- Prove2me | solution 1 for PricingWithTips.minimumTip_eq_requiredTip_off_order_of_plan
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T23:22:32.828973+00:00
-- url     : https://prove2.me/submissions/68ed8903-dbd3-4d9c-85f7-97f0d40456c5

import Theorems.Thm_PricingWithTips_minimumTip_le_requiredTip_off_order

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

private theorem realized_eq_of_trade
    (M : Market B S D) (A : Allocation B S D) (w : B → S → ℝ)
    {d : D} {b : B} {s : S} (ht : A.Trades b s d) :
    courierRealizedUtility M A w d = w b s - M.cost d b s := by
  classical
  have hwork : ∃ b' s', A.Trades b' s' d := ⟨b, s, ht⟩
  unfold courierRealizedUtility
  rw [dif_pos hwork]
  let b₀ := Classical.choose hwork
  let hs := Classical.choose_spec hwork
  let s₀ := Classical.choose hs
  have ht₀ : A.Trades b₀ s₀ d := Classical.choose_spec hs
  have hb : b₀ = b := A.courier_unique ht₀ ht
  have ht₀' : A.Trades b s₀ d := by simpa only [hb] using ht₀
  have hpair : (s₀, d) = (s, d) := by
    exact Option.some.inj (ht₀'.symm.trans ht)
  have hss : s₀ = s := congrArg Prod.fst hpair
  change w b₀ s₀ - M.cost d b₀ s₀ = w b s - M.cost d b s
  rw [hb, hss]

theorem solution [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (w : B → S → ℝ) (uBar : D → ℝ)
    (hplan : IsCourierPlanFor M A w)
    (hreal : ∀ d, courierRealizedUtility M A w d = uBar d)
    (b : B) (s : S) (hoff : ¬ A.Delivers b s) :
    minimumTip M w (fun _ _ => 0) b s = requiredTip M A uBar b s := by
  classical
  have hwzero : w b s = 0 := hplan.2.2.2 b s hoff
  have hbounds := plan_realized_bounds M A w hplan
  have hu_nonneg : ∀ d, 0 ≤ uBar d := by
    intro d
    rw [← hreal d]
    exact hbounds.1 d
  have hupper : ∀ d b' s', w b' s' - M.cost d b' s' ≤ uBar d := by
    intro d b' s'
    rw [← hreal d]
    exact hbounds.2 d b' s'
  apply le_antisymm
  · exact minimumTip_le_requiredTip_off_order M A w uBar b s
      hoff hwzero hu_nonneg hupper
  · let T : Set ℝ :=
      {τ | 0 ≤ τ ∧ ∃ d, CourierAccepts M w (fun _ _ => 0) b s τ d}
    have hT_nonempty : T.Nonempty := by
      let d₀ : D := Classical.choice inferInstance
      let τ₀ : ℝ := M.cost d₀ b s + uBar d₀
      refine ⟨τ₀, ?_⟩
      have hτnonneg : 0 ≤ τ₀ := by
        dsimp [τ₀]
        linarith [M.cost_nonneg d₀ b s, hu_nonneg d₀]
      refine ⟨hτnonneg, d₀, ?_⟩
      constructor
      · dsimp [τ₀]
        rw [hwzero]
        linarith [hu_nonneg d₀]
      · intro b' s'
        by_cases hb : b' = b
        · subst b'
          by_cases hs : s' = s
          · subst s'
            simp [counterfactualTip]
          · simp [counterfactualTip, hs, hwzero, τ₀]
            linarith [hupper d₀ b s']
        · simp [counterfactualTip, hb, hwzero, τ₀]
          linarith [hupper d₀ b' s']
    simp only [requiredTip, if_neg hoff]
    change (⨅ d, M.cost d b s + uBar d) ≤ sInf T
    apply le_csInf hT_nonempty
    intro τ hτ
    obtain ⟨_, d, haccept⟩ := hτ
    have hinf : (⨅ d', M.cost d' b s + uBar d') ≤
        M.cost d b s + uBar d := by
      exact ciInf_le (Finite.bddBelow_range _) d
    have htarget := haccept.1
    by_cases hwork : A.CourierWorks d
    · obtain ⟨b₀, s₀, htrade⟩ := hwork
      have hneq : (b₀, s₀) ≠ (b, s) := by
        rintro ⟨rfl, rfl⟩
        exact hoff ⟨d, htrade⟩
      have hctip : counterfactualTip (fun _ _ => 0) b s τ b₀ s₀ = 0 := by
        by_cases hb : b₀ = b
        · subst b₀
          have hs : s₀ ≠ s := by
            intro he
            exact hneq (by simp [he])
          simp [counterfactualTip, hs]
        · simp [counterfactualTip, hb]
      have hcomp := haccept.2 b₀ s₀
      rw [hctip] at hcomp
      have hrealtrade := realized_eq_of_trade M A w htrade
      rw [hreal d] at hrealtrade
      rw [hwzero] at hcomp
      linarith
    · have hrealzero : uBar d = 0 := by
        rw [← hreal d]
        change ¬ ∃ b s, A.Trades b s d at hwork
        simp [courierRealizedUtility, hwork]
      rw [hwzero] at htarget
      linarith


