-- Prove2me | solution 1 for PricingWithTips.sold_store_alternatives_le
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:42:43.075988+00:00
-- url     : https://prove2.me/submissions/c792bc74-de68-4f49-9c84-fb7de87164a7

import Theorems.Thm_PricingWithTips_assigned_order_courier_envelope
import Theorems.Thm_PricingWithTips_adjustedValue_store_off_order

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D] [Nonempty D]

private noncomputable def soldStoreCourier (A : Allocation B S D) (s : S) : D := by
  classical
  exact if h : A.Sells s then Classical.choose (Classical.choose_spec h)
    else Classical.choice inferInstance

private theorem soldStoreCourier_trades
    (A : Allocation B S D) {s : S} (hs : A.Sells s) :
    ∃ b, A.Trades b s (soldStoreCourier A s) := by
  classical
  let b := Classical.choose hs
  let hd := Classical.choose_spec hs
  refine ⟨b, ?_⟩
  simpa [soldStoreCourier, hs] using (Classical.choose_spec hd)

private theorem soldStoreCourier_injective
    (A : Allocation B S D) {s₁ s₂ : S}
    (hs₁ : A.Sells s₁) (hs₂ : A.Sells s₂)
    (he : soldStoreCourier A s₁ = soldStoreCourier A s₂) : s₁ = s₂ := by
  obtain ⟨b₁,ht₁⟩ := soldStoreCourier_trades A hs₁
  obtain ⟨b₂,ht₂⟩ := soldStoreCourier_trades A hs₂
  have ht₁' : A.Trades b₁ s₁ (soldStoreCourier A s₂) := by simpa only [he] using ht₁
  have hb : b₁ = b₂ := A.courier_unique ht₁' ht₂
  have ht₁'' : A.Trades b₂ s₁ (soldStoreCourier A s₂) := by simpa only [hb] using ht₁'
  have hp : some (s₁,soldStoreCourier A s₂) =
      some (s₂,soldStoreCourier A s₂) := ht₁''.symm.trans ht₂
  exact congrArg Prod.fst (Option.some.inj hp)

private theorem soldStoreCourier_eq_of_trade
    (A : Allocation B S D) {b : B} {s : S} {d : D}
    (ht : A.Trades b s d) : soldStoreCourier A s = d := by
  have hs : A.Sells s := ⟨b,d,ht⟩
  obtain ⟨b₀,ht₀⟩ := soldStoreCourier_trades A hs
  have hb : b₀ = b := A.store_unique ht₀ ht
  have ht₀' : A.Trades b s (soldStoreCourier A s) := by simpa only [hb] using ht₀
  have hp : some (s,soldStoreCourier A s) = some (s,d) := ht₀'.symm.trans ht
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

private theorem soldStoreCourier_min_surcharge
    (M : Market B S D) (A : Allocation B S D)
    (cBS : B → S → ℝ) (cDS : D → S → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDS d s)
    (w : B → S → ℝ) (uBar : D → ℝ)
    (hplan : IsCourierPlanFor M A w)
    (hreal : ∀ d, courierRealizedUtility M A w d = uBar d)
    {s : S} (hs : A.Sells s) :
    (⨅ d : D, cDS d s + uBar d) =
      cDS (soldStoreCourier A s) s + uBar (soldStoreCourier A s) := by
  classical
  let d₀ := soldStoreCourier A s
  obtain ⟨b₀,ht₀⟩ := soldStoreCourier_trades A hs
  have henv := assigned_order_courier_envelope M A w uBar hplan hreal ht₀
  have hw : w b₀ s = M.cost d₀ b₀ s + uBar d₀ := by
    have hr := hreal d₀
    rw [realized_eq_trade' M A w ht₀] at hr
    linarith
  have hall : ∀ d, cDS d₀ s + uBar d₀ ≤ cDS d s + uBar d := by
    intro d
    have hle : (⨅ d' : D, M.cost d' b₀ s + uBar d') ≤
        M.cost d b₀ s + uBar d := ciInf_le (Finite.bddBelow_range _) d
    rw [henv, hw, hcost d₀ b₀ s, hcost d b₀ s] at hle
    linarith
  apply le_antisymm
  · exact ciInf_le (Finite.bddBelow_range _) d₀
  · exact le_ciInf hall

private theorem adjustedValue_sold_store_off_cost
    (M : Market B S D) (A : Allocation B S D)
    (cBS : B → S → ℝ) (cDS : D → S → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDS d s)
    (w : B → S → ℝ) (uBar : D → ℝ)
    (hplan : IsCourierPlanFor M A w)
    (hreal : ∀ d, courierRealizedUtility M A w d = uBar d)
    (b : B) (s : S) (hs : A.Sells s) (hoff : ¬ A.Delivers b s) :
    adjustedValue M A uBar b s =
      M.value b s - M.cost (soldStoreCourier A s) b s -
        uBar (soldStoreCourier A s) := by
  rw [adjustedValue_store_off_order M A uBar cBS cDS hcost b s hoff]
  rw [soldStoreCourier_min_surcharge M A cBS cDS hcost w uBar hplan hreal hs]
  rw [hcost]
  ring

private noncomputable def soldStoreMatchingAllocation
    (A : Allocation B S D) (z : BuyerMatching B S)
    (hused : ∀ b s, z.assigned b = some s → A.Sells s) : Allocation B S D where
  assigned := fun b => (z.assigned b).map (fun s => (s, soldStoreCourier A s))
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
    have hd₁ : soldStoreCourier A t₁ = d := congrArg Prod.snd hp₁
    have hd₂ : soldStoreCourier A t₂ = d := congrArg Prod.snd hp₂
    have hs : t₁ = t₂ := soldStoreCourier_injective A
      (hused b₁ t₁ hz₁) (hused b₂ t₂ hz₂) (hd₁.trans hd₂.symm)
    subst t₂
    exact z.store_unique hz₁ hz₂

theorem sold_store_alternatives_le [Nonempty B]
    (M : Market B S D) (A : Allocation B S D)
    (cBS : B → S → ℝ) (cDS : D → S → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDS d s)
    (hoptimal : IsWelfareOptimal M A)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar)
    (z : BuyerMatching B S)
    (hused : ∀ b s, z.assigned b = some s → A.Sells s) :
    matchingWeight z (adjustedValue M A uBar) ≤
      matchingWeight A.toBuyerMatching (adjustedValue M A uBar) := by
  classical
  obtain ⟨w,hplan,hreal⟩ := hu.1
  let q := adjustedValue M A uBar
  have hu_store : ∀ s, A.Sells s → 0 ≤ uBar (soldStoreCourier A s) := by
    intro s hs
    obtain ⟨b,ht⟩ := soldStoreCourier_trades A hs
    have h := (hplan.2.1 (soldStoreCourier A s) b s ht).1
    have hr := hreal (soldStoreCourier A s)
    rw [realized_eq_trade' M A w ht] at hr
    linarith
  let A' := soldStoreMatchingAllocation A z hused
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
        | none => simp [q, A', soldStoreMatchingAllocation, Allocation.toBuyerMatching, ha, hz]
        | some s =>
            have hs := hused b s hz
            have hoff : ¬ A.Delivers b s := by
              rintro ⟨d,ht⟩
              simp [Allocation.Trades, ha] at ht
            have hq := adjustedValue_sold_store_off_cost M A cBS cDS
              hcost w uBar hplan hreal b s hs hoff
            simp only [A', soldStoreMatchingAllocation, Allocation.toBuyerMatching,
              ha, hz, Option.map_none, Option.map_some, q] at *
            rw [hq]
            linarith [hu_store s hs]
    | some sd =>
        rcases sd with ⟨s₀,d₀⟩
        have ht₀ : A.Trades b s₀ d₀ := ha
        have hq₀ : q b s₀ = M.value b s₀ := by
          have hd : A.Delivers b s₀ := ⟨d₀,ht₀⟩
          simp [q, adjustedValue, requiredTip, hd]
        cases hz : z.assigned b with
        | none =>
            simp [A', soldStoreMatchingAllocation, Allocation.toBuyerMatching,
              ha, hz, hq₀]
            exact M.cost_nonneg d₀ b s₀
        | some s =>
            by_cases hs : s = s₀
            · subst s
              have hd : soldStoreCourier A s₀ = d₀ :=
                soldStoreCourier_eq_of_trade A ht₀
              simp [A', soldStoreMatchingAllocation, Allocation.toBuyerMatching,
                ha, hz, hd]
            · have hstore := hused b s hz
              have hoff : ¬ A.Delivers b s := by
                rintro ⟨d,ht⟩
                have hp : some (s,d) = some (s₀,d₀) := ht.symm.trans ht₀
                exact hs (congrArg Prod.fst (Option.some.inj hp))
              have hq := adjustedValue_sold_store_off_cost M A cBS cDS
                hcost w uBar hplan hreal b s hstore hoff
              simp only [A', soldStoreMatchingAllocation, Allocation.toBuyerMatching,
                ha, hz, Option.map_some, q] at *
              rw [hq, hq₀]
              linarith [hu_store s hstore, M.cost_nonneg d₀ b s₀]
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
    (cBS : B → S → ℝ) (cDS : D → S → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDS d s)
    (hoptimal : PricingWithTips.IsWelfareOptimal M A)
    (uBar : D → ℝ) (hu : PricingWithTips.IsMaximalCourierUtility M A uBar)
    (z : PricingWithTips.BuyerMatching B S)
    (hused : ∀ b s, z.assigned b = some s → A.Sells s) :
    PricingWithTips.matchingWeight z (PricingWithTips.adjustedValue M A uBar) ≤
      PricingWithTips.matchingWeight A.toBuyerMatching
        (PricingWithTips.adjustedValue M A uBar) := by
  exact PricingWithTips.sold_store_alternatives_le
    M A cBS cDS hcost hoptimal uBar hu z hused
