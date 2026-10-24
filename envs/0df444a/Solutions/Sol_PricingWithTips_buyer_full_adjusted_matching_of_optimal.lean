-- Prove2me | solution 1 for PricingWithTips.buyer_full_adjusted_matching_of_optimal
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:37:03.852831+00:00
-- url     : https://prove2.me/submissions/7fcfc43e-1c8a-4c58-9c7c-2bd692b91b23

import Theorems.Thm_PricingWithTips_assigned_order_courier_envelope
import Theorems.Thm_PricingWithTips_adjustedValue_buyer_off_order

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

private noncomputable def buyerCourier (A : Allocation B S D)
    (hfull : ∀ b, ∃ s d, A.Trades b s d) (b : B) : D := by
  classical
  exact Classical.choose (Classical.choose_spec (hfull b))

private theorem buyerCourier_trades
    (A : Allocation B S D) (hfull : ∀ b, ∃ s d, A.Trades b s d) (b : B) :
    ∃ s, A.Trades b s (buyerCourier A hfull b) := by
  classical
  let s := Classical.choose (hfull b)
  let hd := Classical.choose_spec (hfull b)
  exact ⟨s, Classical.choose_spec hd⟩

private theorem buyerCourier_injective
    (A : Allocation B S D) (hfull : ∀ b, ∃ s d, A.Trades b s d) :
    Function.Injective (buyerCourier A hfull) := by
  intro b₁ b₂ he
  obtain ⟨s₁,ht₁⟩ := buyerCourier_trades A hfull b₁
  obtain ⟨s₂,ht₂⟩ := buyerCourier_trades A hfull b₂
  have ht₁' : A.Trades b₁ s₁ (buyerCourier A hfull b₂) := by
    simpa only [he] using ht₁
  exact A.courier_unique ht₁' ht₂

private theorem buyerCourier_eq_of_trade
    (A : Allocation B S D) (hfull : ∀ b, ∃ s d, A.Trades b s d)
    {b : B} {s : S} {d : D} (ht : A.Trades b s d) :
    buyerCourier A hfull b = d := by
  obtain ⟨s₀,ht₀⟩ := buyerCourier_trades A hfull b
  have hp : some (s₀,buyerCourier A hfull b) = some (s,d) := ht₀.symm.trans ht
  exact congrArg Prod.snd (Option.some.inj hp)

private theorem realized_eq_trade'
    (M : Market B S D) (A : Allocation B S D) (w : B → S → ℝ)
    {d : D} {b : B} {s : S} (ht : A.Trades b s d) :
    courierRealizedUtility M A w d = w b s - M.cost d b s := by
  classical
  have hwork : ∃ b' s', A.Trades b' s' d := ⟨b,s,ht⟩
  unfold courierRealizedUtility
  rw [dif_pos hwork]
  let b₀ := Classical.choose hwork
  let hs := Classical.choose_spec hwork
  let s₀ := Classical.choose hs
  have ht₀ : A.Trades b₀ s₀ d := Classical.choose_spec hs
  have hb : b₀ = b := A.courier_unique ht₀ ht
  have ht₀' : A.Trades b s₀ d := by simpa only [hb] using ht₀
  have hpair : (s₀,d) = (s,d) := Option.some.inj (ht₀'.symm.trans ht)
  have hss : s₀ = s := congrArg Prod.fst hpair
  change w b₀ s₀ - M.cost d b₀ s₀ = w b s - M.cost d b s
  rw [hb,hss]

theorem buyerCourier_min_surcharge [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ b, ∃ s d, A.Trades b s d)
    (cBS : B → S → ℝ) (cDB : D → B → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDB d b)
    (w : B → S → ℝ) (uBar : D → ℝ)
    (hplan : IsCourierPlanFor M A w)
    (hreal : ∀ d, courierRealizedUtility M A w d = uBar d)
    (b : B) :
    (⨅ d : D, cDB d b + uBar d) =
      cDB (buyerCourier A hfull b) b + uBar (buyerCourier A hfull b) := by
  classical
  let d₀ := buyerCourier A hfull b
  obtain ⟨s₀,ht₀⟩ := buyerCourier_trades A hfull b
  have henv := assigned_order_courier_envelope M A w uBar hplan hreal ht₀
  have hw : w b s₀ = M.cost d₀ b s₀ + uBar d₀ := by
    have hreal₀ := hreal d₀
    rw [realized_eq_trade' M A w ht₀] at hreal₀
    linarith
  have hall : ∀ d, cDB d₀ b + uBar d₀ ≤ cDB d b + uBar d := by
    intro d
    have hle : (⨅ d' : D, M.cost d' b s₀ + uBar d') ≤
        M.cost d b s₀ + uBar d := ciInf_le (Finite.bddBelow_range _) d
    rw [henv, hw, hcost d₀ b s₀, hcost d b s₀] at hle
    linarith
  apply le_antisymm
  · exact ciInf_le (Finite.bddBelow_range _) d₀
  · exact le_ciInf hall

theorem adjustedValue_buyer_off_cost [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ b, ∃ s d, A.Trades b s d)
    (cBS : B → S → ℝ) (cDB : D → B → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDB d b)
    (w : B → S → ℝ) (uBar : D → ℝ)
    (hplan : IsCourierPlanFor M A w)
    (hreal : ∀ d, courierRealizedUtility M A w d = uBar d)
    (b : B) (s : S) (hoff : ¬ A.Delivers b s) :
    adjustedValue M A uBar b s =
      M.value b s - M.cost (buyerCourier A hfull b) b s -
        uBar (buyerCourier A hfull b) := by
  rw [adjustedValue_buyer_off_order M A uBar cBS cDB hcost b s hoff]
  rw [buyerCourier_min_surcharge M A hfull cBS cDB hcost w uBar hplan hreal b]
  rw [hcost]
  ring

private noncomputable def buyerMatchingAllocation
    (A : Allocation B S D) (hfull : ∀ b, ∃ s d, A.Trades b s d)
    (z : BuyerMatching B S) : Allocation B S D where
  assigned := fun b => (z.assigned b).map (fun s => (s, buyerCourier A hfull b))
  store_unique := by
    intro b₁ b₂ s d₁ d₂ h₁ h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨s₁,hz₁,hp₁⟩ := h₁
    obtain ⟨s₂,hz₂,hp₂⟩ := h₂
    have hs₁ : s₁ = s := congrArg Prod.fst hp₁
    have hs₂ : s₂ = s := congrArg Prod.fst hp₂
    exact z.store_unique (by simpa [hs₁] using hz₁) (by simpa [hs₂] using hz₂)
  courier_unique := by
    intro b₁ b₂ s₁ s₂ d h₁ h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨t₁,hz₁,hp₁⟩ := h₁
    obtain ⟨t₂,hz₂,hp₂⟩ := h₂
    have hd₁ : buyerCourier A hfull b₁ = d := congrArg Prod.snd hp₁
    have hd₂ : buyerCourier A hfull b₂ = d := congrArg Prod.snd hp₂
    exact buyerCourier_injective A hfull (hd₁.trans hd₂.symm)

theorem buyer_full_adjusted_matching_of_optimal [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ b, ∃ s d, A.Trades b s d)
    (cBS : B → S → ℝ) (cDB : D → B → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDB d b)
    (hoptimal : IsWelfareOptimal M A)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar) :
    IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by
  classical
  obtain ⟨w,hplan,hreal⟩ := hu.1
  let q := adjustedValue M A uBar
  have hu_buyer : ∀ b, 0 ≤ uBar (buyerCourier A hfull b) := by
    intro b
    obtain ⟨s,ht⟩ := buyerCourier_trades A hfull b
    have h := (hplan.2.1 (buyerCourier A hfull b) b s ht).1
    have hr := hreal (buyerCourier A hfull b)
    rw [realized_eq_trade' M A w ht] at hr
    linarith
  intro z
  let A' := buyerMatchingAllocation A hfull z
  have hpoint : ∀ b,
      (match z.assigned b with
        | none => 0
        | some s => q b s) -
      (match A.toBuyerMatching.assigned b with
        | none => 0
        | some s => q b s) ≤
      (match A'.assigned b with
        | none => 0
        | some (s,d) => M.value b s - M.cost d b s) -
      (match A.assigned b with
        | none => 0
        | some (s,d) => M.value b s - M.cost d b s) := by
    intro b
    obtain ⟨s₀,d₀,ht₀⟩ := hfull b
    have ha : A.assigned b = some (s₀,d₀) := ht₀
    have hq₀ : q b s₀ = M.value b s₀ := by
      have hd : A.Delivers b s₀ := ⟨d₀,ht₀⟩
      simp [q, adjustedValue, requiredTip, hd]
    cases hz : z.assigned b with
    | none =>
        simp [A', buyerMatchingAllocation, Allocation.toBuyerMatching,
          ha, hz, hq₀]
        exact M.cost_nonneg d₀ b s₀
    | some s =>
        by_cases hs : s = s₀
        · subst s
          have hd : buyerCourier A hfull b = d₀ :=
            buyerCourier_eq_of_trade A hfull ht₀
          simp [A', buyerMatchingAllocation, Allocation.toBuyerMatching,
            ha, hz, hd]
        · have hoff : ¬ A.Delivers b s := by
            rintro ⟨d,ht⟩
            have hp : some (s,d) = some (s₀,d₀) := ht.symm.trans ht₀
            exact hs (congrArg Prod.fst (Option.some.inj hp))
          have hq := adjustedValue_buyer_off_cost M A hfull cBS cDB
            hcost w uBar hplan hreal b s hoff
          simp only [A', buyerMatchingAllocation, Allocation.toBuyerMatching,
            ha, hz, Option.map_some, q] at *
          rw [hq, hq₀]
          linarith [hu_buyer b, M.cost_nonneg d₀ b s₀]
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpoint b)
  simp only [Finset.sum_sub_distrib] at hsum
  change matchingWeight z q - matchingWeight A.toBuyerMatching q ≤
    welfare M A' - welfare M A at hsum
  have hopt := hoptimal A'
  exact sub_nonpos.mp (le_trans hsum (sub_nonpos.mpr hopt))

end PricingWithTips

theorem solution {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
    [DecidableEq B] [DecidableEq S] [DecidableEq D] [Nonempty D]
    (M : PricingWithTips.Market B S D) (A : PricingWithTips.Allocation B S D)
    (hfull : ∀ b, ∃ s d, A.Trades b s d)
    (cBS : B → S → ℝ) (cDB : D → B → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDB d b)
    (hoptimal : PricingWithTips.IsWelfareOptimal M A)
    (uBar : D → ℝ) (hu : PricingWithTips.IsMaximalCourierUtility M A uBar) :
    PricingWithTips.IsMaximumWeight A.toBuyerMatching
      (PricingWithTips.adjustedValue M A uBar) := by
  exact PricingWithTips.buyer_full_adjusted_matching_of_optimal
    M A hfull cBS cDB hcost hoptimal uBar hu
