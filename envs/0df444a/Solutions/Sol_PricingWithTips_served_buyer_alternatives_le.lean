-- Prove2me | solution 1 for PricingWithTips.served_buyer_alternatives_le
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:47:49.033492+00:00
-- url     : https://prove2.me/submissions/3deb259f-dc64-4113-86a9-66929b8f1112

import Theorems.Thm_PricingWithTips_assigned_order_courier_envelope
import Theorems.Thm_PricingWithTips_adjustedValue_buyer_off_order

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D] [Nonempty D]

private noncomputable def servedBuyerCourier (A : Allocation B S D) (b : B) : D := by
  classical
  exact if h : ∃ s d, A.Trades b s d then
    Classical.choose (Classical.choose_spec h) else Classical.choice inferInstance

private theorem servedBuyerCourier_trades
    (A : Allocation B S D) {b : B} (hb : ∃ s d, A.Trades b s d) :
    ∃ s, A.Trades b s (servedBuyerCourier A b) := by
  classical
  let s := Classical.choose hb
  let hd := Classical.choose_spec hb
  refine ⟨s, ?_⟩
  simpa [servedBuyerCourier, hb] using (Classical.choose_spec hd)

private theorem servedBuyerCourier_injective
    (A : Allocation B S D) {b₁ b₂ : B}
    (hb₁ : ∃ s d, A.Trades b₁ s d)
    (hb₂ : ∃ s d, A.Trades b₂ s d)
    (he : servedBuyerCourier A b₁ = servedBuyerCourier A b₂) : b₁ = b₂ := by
  obtain ⟨s₁,ht₁⟩ := servedBuyerCourier_trades A hb₁
  obtain ⟨s₂,ht₂⟩ := servedBuyerCourier_trades A hb₂
  have ht₁' : A.Trades b₁ s₁ (servedBuyerCourier A b₂) := by simpa only [he] using ht₁
  exact A.courier_unique ht₁' ht₂

private theorem servedBuyerCourier_eq_of_trade
    (A : Allocation B S D) {b : B} {s : S} {d : D}
    (ht : A.Trades b s d) : servedBuyerCourier A b = d := by
  have hb : ∃ s d, A.Trades b s d := ⟨s,d,ht⟩
  obtain ⟨s₀,ht₀⟩ := servedBuyerCourier_trades A hb
  have hp : some (s₀,servedBuyerCourier A b) = some (s,d) := ht₀.symm.trans ht
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

private theorem servedBuyerCourier_min_surcharge
    (M : Market B S D) (A : Allocation B S D)
    (cBS : B → S → ℝ) (cDB : D → B → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDB d b)
    (w : B → S → ℝ) (uBar : D → ℝ)
    (hplan : IsCourierPlanFor M A w)
    (hreal : ∀ d, courierRealizedUtility M A w d = uBar d)
    {b : B} (hb : ∃ s d, A.Trades b s d) :
    (⨅ d : D, cDB d b + uBar d) =
      cDB (servedBuyerCourier A b) b + uBar (servedBuyerCourier A b) := by
  classical
  let d₀ := servedBuyerCourier A b
  obtain ⟨s₀,ht₀⟩ := servedBuyerCourier_trades A hb
  have henv := assigned_order_courier_envelope M A w uBar hplan hreal ht₀
  have hw : w b s₀ = M.cost d₀ b s₀ + uBar d₀ := by
    have hr := hreal d₀
    rw [realized_eq_trade' M A w ht₀] at hr
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

private theorem adjustedValue_served_buyer_off_cost
    (M : Market B S D) (A : Allocation B S D)
    (cBS : B → S → ℝ) (cDB : D → B → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDB d b)
    (w : B → S → ℝ) (uBar : D → ℝ)
    (hplan : IsCourierPlanFor M A w)
    (hreal : ∀ d, courierRealizedUtility M A w d = uBar d)
    (b : B) (s : S) (hb : ∃ s d, A.Trades b s d)
    (hoff : ¬ A.Delivers b s) :
    adjustedValue M A uBar b s =
      M.value b s - M.cost (servedBuyerCourier A b) b s -
        uBar (servedBuyerCourier A b) := by
  rw [adjustedValue_buyer_off_order M A uBar cBS cDB hcost b s hoff]
  rw [servedBuyerCourier_min_surcharge M A cBS cDB hcost w uBar hplan hreal hb]
  rw [hcost]
  ring

private noncomputable def servedBuyerMatchingAllocation
    (A : Allocation B S D) (z : BuyerMatching B S)
    (hused : ∀ b s, z.assigned b = some s → ∃ s₀ d₀, A.Trades b s₀ d₀) :
    Allocation B S D where
  assigned := fun b => (z.assigned b).map (fun s => (s, servedBuyerCourier A b))
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
    have hd₁ : servedBuyerCourier A b₁ = d := congrArg Prod.snd hp₁
    have hd₂ : servedBuyerCourier A b₂ = d := congrArg Prod.snd hp₂
    exact servedBuyerCourier_injective A
      (hused b₁ t₁ hz₁) (hused b₂ t₂ hz₂) (hd₁.trans hd₂.symm)

theorem served_buyer_alternatives_le [Nonempty B]
    (M : Market B S D) (A : Allocation B S D)
    (cBS : B → S → ℝ) (cDB : D → B → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDB d b)
    (hoptimal : IsWelfareOptimal M A)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar)
    (z : BuyerMatching B S)
    (hused : ∀ b s, z.assigned b = some s → ∃ s₀ d₀, A.Trades b s₀ d₀) :
    matchingWeight z (adjustedValue M A uBar) ≤
      matchingWeight A.toBuyerMatching (adjustedValue M A uBar) := by
  classical
  obtain ⟨w,hplan,hreal⟩ := hu.1
  let q := adjustedValue M A uBar
  have hu_buyer : ∀ b, (∃ s d, A.Trades b s d) →
      0 ≤ uBar (servedBuyerCourier A b) := by
    intro b hb
    obtain ⟨s,ht⟩ := servedBuyerCourier_trades A hb
    have h := (hplan.2.1 (servedBuyerCourier A b) b s ht).1
    have hr := hreal (servedBuyerCourier A b)
    rw [realized_eq_trade' M A w ht] at hr
    linarith
  let A' := servedBuyerMatchingAllocation A z hused
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
    cases ha : A.assigned b with
    | none =>
        cases hz : z.assigned b with
        | none => simp [q, A', servedBuyerMatchingAllocation, Allocation.toBuyerMatching, ha, hz]
        | some s =>
            obtain ⟨s₀,d₀,ht₀⟩ := hused b s hz
            simp [Allocation.Trades, ha] at ht₀
    | some sd =>
        rcases sd with ⟨s₀,d₀⟩
        have ht₀ : A.Trades b s₀ d₀ := ha
        have hb : ∃ s d, A.Trades b s d := ⟨s₀,d₀,ht₀⟩
        have hq₀ : q b s₀ = M.value b s₀ := by
          have hd : A.Delivers b s₀ := ⟨d₀,ht₀⟩
          simp [q, adjustedValue, requiredTip, hd]
        cases hz : z.assigned b with
        | none =>
            simp [A', servedBuyerMatchingAllocation, Allocation.toBuyerMatching,
              ha, hz, hq₀]
            exact M.cost_nonneg d₀ b s₀
        | some s =>
            by_cases hs : s = s₀
            · subst s
              have hd : servedBuyerCourier A b = d₀ :=
                servedBuyerCourier_eq_of_trade A ht₀
              simp [A', servedBuyerMatchingAllocation, Allocation.toBuyerMatching,
                ha, hz, hd]
            · have hoff : ¬ A.Delivers b s := by
                rintro ⟨d,ht⟩
                have hp : some (s,d) = some (s₀,d₀) := ht.symm.trans ht₀
                exact hs (congrArg Prod.fst (Option.some.inj hp))
              have hq := adjustedValue_served_buyer_off_cost M A cBS cDB
                hcost w uBar hplan hreal b s hb hoff
              simp only [A', servedBuyerMatchingAllocation, Allocation.toBuyerMatching,
                ha, hz, Option.map_some, q] at *
              rw [hq, hq₀]
              linarith [hu_buyer b hb, M.cost_nonneg d₀ b s₀]
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpoint b)
  simp only [Finset.sum_sub_distrib] at hsum
  change matchingWeight z q - matchingWeight A.toBuyerMatching q ≤
    welfare M A' - welfare M A at hsum
  have hopt := hoptimal A'
  exact sub_nonpos.mp (le_trans hsum (sub_nonpos.mpr hopt))

end PricingWithTips

theorem solution {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
    [DecidableEq B] [DecidableEq S] [DecidableEq D]
    [Nonempty D] [Nonempty B]
    (M : PricingWithTips.Market B S D) (A : PricingWithTips.Allocation B S D)
    (cBS : B → S → ℝ) (cDB : D → B → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDB d b)
    (hoptimal : PricingWithTips.IsWelfareOptimal M A)
    (uBar : D → ℝ) (hu : PricingWithTips.IsMaximalCourierUtility M A uBar)
    (z : PricingWithTips.BuyerMatching B S)
    (hused : ∀ b s, z.assigned b = some s → ∃ s₀ d₀, A.Trades b s₀ d₀) :
    PricingWithTips.matchingWeight z (PricingWithTips.adjustedValue M A uBar) ≤
      PricingWithTips.matchingWeight A.toBuyerMatching
        (PricingWithTips.adjustedValue M A uBar) := by
  exact PricingWithTips.served_buyer_alternatives_le
    M A cBS cDB hcost hoptimal uBar hu z hused
