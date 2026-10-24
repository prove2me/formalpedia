-- Prove2me | solution 1 for PricingWithTips.store_full_adjusted_matching_of_optimal
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:31:44.858346+00:00
-- url     : https://prove2.me/submissions/7d4a483d-3363-4546-bc53-8b88fb11c197

import Theorems.Thm_PricingWithTips_assigned_order_courier_envelope
import Theorems.Thm_PricingWithTips_adjustedValue_store_off_order

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

private noncomputable def storeCourier (A : Allocation B S D)
    (hfull : ∀ s, A.Sells s) (s : S) : D := by
  classical
  exact Classical.choose (Classical.choose_spec (hfull s))

private theorem storeCourier_trades
    (A : Allocation B S D) (hfull : ∀ s, A.Sells s) (s : S) :
    ∃ b, A.Trades b s (storeCourier A hfull s) := by
  classical
  let b := Classical.choose (hfull s)
  let hd := Classical.choose_spec (hfull s)
  exact ⟨b, Classical.choose_spec hd⟩

private theorem storeCourier_injective
    (A : Allocation B S D) (hfull : ∀ s, A.Sells s) :
    Function.Injective (storeCourier A hfull) := by
  intro s₁ s₂ he
  obtain ⟨b₁,ht₁⟩ := storeCourier_trades A hfull s₁
  obtain ⟨b₂,ht₂⟩ := storeCourier_trades A hfull s₂
  have ht₁' : A.Trades b₁ s₁ (storeCourier A hfull s₂) := by
    simpa only [he] using ht₁
  have hb : b₁ = b₂ := A.courier_unique ht₁' ht₂
  have ht₁'' : A.Trades b₂ s₁ (storeCourier A hfull s₂) := by
    simpa only [hb] using ht₁'
  have hp : some (s₁,storeCourier A hfull s₂) =
      some (s₂,storeCourier A hfull s₂) := ht₁''.symm.trans ht₂
  exact congrArg Prod.fst (Option.some.inj hp)

private theorem storeCourier_eq_of_trade
    (A : Allocation B S D) (hfull : ∀ s, A.Sells s)
    {b : B} {s : S} {d : D} (ht : A.Trades b s d) :
    storeCourier A hfull s = d := by
  obtain ⟨b₀,ht₀⟩ := storeCourier_trades A hfull s
  have hb : b₀ = b := A.store_unique ht₀ ht
  have ht₀' : A.Trades b s (storeCourier A hfull s) := by
    simpa only [hb] using ht₀
  have hp : some (s,storeCourier A hfull s) = some (s,d) := ht₀'.symm.trans ht
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

theorem storeCourier_min_surcharge [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ s, A.Sells s)
    (cBS : B → S → ℝ) (cDS : D → S → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDS d s)
    (w : B → S → ℝ) (uBar : D → ℝ)
    (hplan : IsCourierPlanFor M A w)
    (hreal : ∀ d, courierRealizedUtility M A w d = uBar d)
    (s : S) :
    (⨅ d : D, cDS d s + uBar d) =
      cDS (storeCourier A hfull s) s + uBar (storeCourier A hfull s) := by
  classical
  let d₀ := storeCourier A hfull s
  obtain ⟨b₀,ht₀⟩ := storeCourier_trades A hfull s
  have henv := assigned_order_courier_envelope M A w uBar hplan hreal ht₀
  have hw : w b₀ s = M.cost d₀ b₀ s + uBar d₀ := by
    have hreal₀ := hreal d₀
    rw [realized_eq_trade' M A w ht₀] at hreal₀
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

theorem adjustedValue_store_off_cost [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ s, A.Sells s)
    (cBS : B → S → ℝ) (cDS : D → S → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDS d s)
    (w : B → S → ℝ) (uBar : D → ℝ)
    (hplan : IsCourierPlanFor M A w)
    (hreal : ∀ d, courierRealizedUtility M A w d = uBar d)
    (b : B) (s : S) (hoff : ¬ A.Delivers b s) :
    adjustedValue M A uBar b s =
      M.value b s - M.cost (storeCourier A hfull s) b s -
        uBar (storeCourier A hfull s) := by
  rw [adjustedValue_store_off_order M A uBar cBS cDS hcost b s hoff]
  rw [storeCourier_min_surcharge M A hfull cBS cDS hcost w uBar hplan hreal s]
  rw [hcost]
  ring

private noncomputable def storeMatchingAllocation
    (A : Allocation B S D) (hfull : ∀ s, A.Sells s)
    (z : BuyerMatching B S) : Allocation B S D where
  assigned := fun b => (z.assigned b).map (fun s => (s, storeCourier A hfull s))
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
    have hd₁ : storeCourier A hfull t₁ = d := congrArg Prod.snd hp₁
    have hd₂ : storeCourier A hfull t₂ = d := congrArg Prod.snd hp₂
    have hs : t₁ = t₂ := storeCourier_injective A hfull (hd₁.trans hd₂.symm)
    subst t₂
    exact z.store_unique hz₁ hz₂

theorem store_full_adjusted_matching_of_optimal [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ s, A.Sells s)
    (cBS : B → S → ℝ) (cDS : D → S → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDS d s)
    (hoptimal : IsWelfareOptimal M A)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar) :
    IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by
  classical
  obtain ⟨w,hplan,hreal⟩ := hu.1
  let q := adjustedValue M A uBar
  have hu_store : ∀ s, 0 ≤ uBar (storeCourier A hfull s) := by
    intro s
    obtain ⟨b,ht⟩ := storeCourier_trades A hfull s
    have h := (hplan.2.1 (storeCourier A hfull s) b s ht).1
    have hr := hreal (storeCourier A hfull s)
    rw [realized_eq_trade' M A w ht] at hr
    linarith
  intro z
  let A' := storeMatchingAllocation A hfull z
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
        | none => simp [q, A', storeMatchingAllocation, Allocation.toBuyerMatching, ha, hz]
        | some s =>
            have hoff : ¬ A.Delivers b s := by
              rintro ⟨d,ht⟩
              simp [Allocation.Trades, ha] at ht
            have hq := adjustedValue_store_off_cost M A hfull cBS cDS
              hcost w uBar hplan hreal b s hoff
            simp only [A', storeMatchingAllocation, Allocation.toBuyerMatching,
              ha, hz, Option.map_none, Option.map_some, q] at *
            rw [hq]
            linarith [hu_store s]
    | some sd =>
        rcases sd with ⟨s₀,d₀⟩
        have ht₀ : A.Trades b s₀ d₀ := ha
        have hq₀ : q b s₀ = M.value b s₀ := by
          have hd : A.Delivers b s₀ := ⟨d₀,ht₀⟩
          simp [q, adjustedValue, requiredTip, hd]
        cases hz : z.assigned b with
        | none =>
            simp [A', storeMatchingAllocation, Allocation.toBuyerMatching,
              ha, hz, hq₀]
            exact M.cost_nonneg d₀ b s₀
        | some s =>
            by_cases hs : s = s₀
            · subst s
              have hd : storeCourier A hfull s₀ = d₀ :=
                storeCourier_eq_of_trade A hfull ht₀
              simp [A', storeMatchingAllocation, Allocation.toBuyerMatching,
                ha, hz, hd]
            · have hoff : ¬ A.Delivers b s := by
                rintro ⟨d,ht⟩
                have hp : some (s,d) = some (s₀,d₀) := ht.symm.trans ht₀
                exact hs (congrArg Prod.fst (Option.some.inj hp))
              have hq := adjustedValue_store_off_cost M A hfull cBS cDS
                hcost w uBar hplan hreal b s hoff
              simp only [A', storeMatchingAllocation, Allocation.toBuyerMatching,
                ha, hz, Option.map_some, q] at *
              rw [hq, hq₀]
              linarith [hu_store s, M.cost_nonneg d₀ b s₀]
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
    (hfull : ∀ s, A.Sells s)
    (cBS : B → S → ℝ) (cDS : D → S → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDS d s)
    (hoptimal : PricingWithTips.IsWelfareOptimal M A)
    (uBar : D → ℝ) (hu : PricingWithTips.IsMaximalCourierUtility M A uBar) :
    PricingWithTips.IsMaximumWeight A.toBuyerMatching
      (PricingWithTips.adjustedValue M A uBar) := by
  exact PricingWithTips.store_full_adjusted_matching_of_optimal
    M A hfull cBS cDS hcost hoptimal uBar hu
