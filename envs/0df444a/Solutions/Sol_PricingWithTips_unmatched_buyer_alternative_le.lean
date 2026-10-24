-- Prove2me | solution 1 for PricingWithTips.unmatched_buyer_alternative_le
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T02:41:26.761871+00:00
-- url     : https://prove2.me/submissions/a376cd7e-f52f-4a93-af2c-1b0c343f183c

import Theorems.Thm_PricingWithTips_assigned_order_courier_envelope
import Theorems.Thm_PricingWithTips_adjustedValue_store_off_order
import Mathlib
import Definitions.Def_AssignmentGame_CoreCorners_Game
import Definitions.Def_PricingWithTips_Model
import Theorems.Thm_PricingWithTips_optimal_reassign_couriers_cost_le
import Theorems.Thm_AssignmentGame_CoreCorners_core_nonempty
import Theorems.Thm_AssignmentGame_CoreCorners_core_dual_constraints
import Theorems.Thm_AssignmentGame_CoreCorners_worth_le_permutation_bound

/- Source: Scratch_PricingWithTips_sold_store_alternatives.lean -/

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D] [Nonempty D]

noncomputable def soldStoreCourier (A : Allocation B S D) (s : S) : D := by
  classical
  exact if h : A.Sells s then Classical.choose (Classical.choose_spec h)
    else Classical.choice inferInstance

theorem soldStoreCourier_trades
    (A : Allocation B S D) {s : S} (hs : A.Sells s) :
    ∃ b, A.Trades b s (soldStoreCourier A s) := by
  classical
  let b := Classical.choose hs
  let hd := Classical.choose_spec hs
  refine ⟨b, ?_⟩
  simpa [soldStoreCourier, hs] using (Classical.choose_spec hd)

theorem soldStoreCourier_injective
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

theorem soldStoreCourier_eq_of_trade
    (A : Allocation B S D) {b : B} {s : S} {d : D}
    (ht : A.Trades b s d) : soldStoreCourier A s = d := by
  have hs : A.Sells s := ⟨b,d,ht⟩
  obtain ⟨b₀,ht₀⟩ := soldStoreCourier_trades A hs
  have hb : b₀ = b := A.store_unique ht₀ ht
  have ht₀' : A.Trades b s (soldStoreCourier A s) := by simpa only [hb] using ht₀
  have hp : some (s,soldStoreCourier A s) = some (s,d) := ht₀'.symm.trans ht
  exact congrArg Prod.snd (Option.some.inj hp)

theorem realized_eq_trade'
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

theorem adjustedValue_sold_store_off_cost
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

theorem sold_store_alternatives_solution {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
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

/- Source: Scratch_AssignmentGame_core_corners_accepted.lean -/

set_option autoImplicit false

/-! ## Basic facts about `worth` and matchings -/

open AssignmentGame.CoreCorners in
theorem ag1171_mem_matchings {M N : Type*} {A : Finset M} {B : Finset N} {P : Finset (M × N)}
    (h : IsMatching A B P) : P ∈ matchings A B := by
  classical
  unfold matchings
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨h.1, h⟩

open AssignmentGame.CoreCorners in
theorem ag1171_isMatching_of_mem {M N : Type*} {A : Finset M} {B : Finset N} {P : Finset (M × N)}
    (h : P ∈ matchings A B) : IsMatching A B P := by
  classical
  unfold matchings at h
  rw [Finset.mem_filter] at h
  exact h.2

open AssignmentGame.CoreCorners in
theorem ag1171_le_worth {M N : Type*} (a : M → N → ℝ) {A : Finset M} {B : Finset N}
    {P : Finset (M × N)} (h : IsMatching A B P) :
    ∑ p ∈ P, a p.1 p.2 ≤ worth a A B := by
  unfold worth
  exact Finset.le_sup' (fun P => ∑ p ∈ P, a p.1 p.2) (ag1171_mem_matchings h)

open AssignmentGame.CoreCorners in
theorem ag1171_exists_opt {M N : Type*} (a : M → N → ℝ) (A : Finset M) (B : Finset N) :
    ∃ P : Finset (M × N), IsMatching A B P ∧ worth a A B = ∑ p ∈ P, a p.1 p.2 := by
  unfold worth
  obtain ⟨P, hP, heq⟩ := Finset.exists_mem_eq_sup' (⟨∅, empty_mem_matchings A B⟩ :
    (matchings A B).Nonempty) (fun P => ∑ p ∈ P, a p.1 p.2)
  exact ⟨P, ag1171_isMatching_of_mem hP, heq⟩

open AssignmentGame.CoreCorners in
theorem ag1171_worth_nonneg {M N : Type*} (a : M → N → ℝ) (A : Finset M) (B : Finset N) :
    0 ≤ worth a A B := by
  have h : IsMatching A B (∅ : Finset (M × N)) := by
    refine ⟨by simp, ?_, ?_⟩ <;> simp
  simpa using ag1171_le_worth a h

open AssignmentGame.CoreCorners in
theorem ag1171_worth_le {M N : Type*} (a : M → N → ℝ) (A : Finset M) (B : Finset N) (c : ℝ)
    (h : ∀ P : Finset (M × N), IsMatching A B P → ∑ p ∈ P, a p.1 p.2 ≤ c) :
    worth a A B ≤ c := by
  obtain ⟨P, hP, hw⟩ := ag1171_exists_opt a A B
  rw [hw]
  exact h P hP

/-- dual feasibility -/
def ag1171_DF {M N : Type*} (a : M → N → ℝ) (u : M → ℝ) (v : N → ℝ) : Prop :=
  (∀ i, 0 ≤ u i) ∧ (∀ j, 0 ≤ v j) ∧ ∀ i j, a i j ≤ u i + v j

open AssignmentGame.CoreCorners in
theorem ag1171_matching_sum_le {M N : Type*} (a : M → N → ℝ) (u : M → ℝ) (v : N → ℝ)
    (h : ag1171_DF a u v) {A : Finset M} {B : Finset N} {P : Finset (M × N)}
    (hP : IsMatching A B P) :
    ∑ p ∈ P, a p.1 p.2 ≤ ∑ i ∈ A, u i + ∑ j ∈ B, v j := by
  classical
  obtain ⟨hsub, h1, h2⟩ := hP
  obtain ⟨hu, hv, hab⟩ := h
  have e1 : ∑ p ∈ P, u p.1 = ∑ i ∈ P.image Prod.fst, u i := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact h1 p hp q hq hpq
  have e2 : ∑ p ∈ P, v p.2 = ∑ j ∈ P.image Prod.snd, v j := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact h2 p hp q hq hpq
  have s1 : ∑ i ∈ P.image Prod.fst, u i ≤ ∑ i ∈ A, u i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
      exact (Finset.mem_product.1 (hsub hp)).1
    · intro i _ _; exact hu i
  have s2 : ∑ j ∈ P.image Prod.snd, v j ≤ ∑ j ∈ B, v j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hj
      exact (Finset.mem_product.1 (hsub hp)).2
    · intro j _ _; exact hv j
  calc ∑ p ∈ P, a p.1 p.2 ≤ ∑ p ∈ P, (u p.1 + v p.2) :=
        Finset.sum_le_sum fun p _ => hab p.1 p.2
    _ = ∑ p ∈ P, u p.1 + ∑ p ∈ P, v p.2 := Finset.sum_add_distrib
    _ ≤ ∑ i ∈ A, u i + ∑ j ∈ B, v j := by rw [e1, e2]; exact add_le_add s1 s2

open AssignmentGame.CoreCorners in
theorem ag1171_core_iff {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (u : M → ℝ) (v : N → ℝ) :
    (u, v) ∈ core a ↔ ag1171_DF a u v ∧ ∑ i, u i + ∑ j, v j = worth a Finset.univ Finset.univ := by
  classical
  constructor
  · rintro ⟨hsum, hcore⟩
    refine ⟨⟨?_, ?_, ?_⟩, hsum⟩
    · intro i
      have := hcore {i} ∅
      have h0 := ag1171_worth_nonneg a {i} (∅ : Finset N)
      simp only [Finset.sum_singleton, Finset.sum_empty, add_zero] at this
      linarith
    · intro j
      have := hcore ∅ {j}
      have h0 := ag1171_worth_nonneg a (∅ : Finset M) {j}
      simp only [Finset.sum_singleton, Finset.sum_empty, zero_add] at this
      linarith
    · intro i j
      have := hcore {i} {j}
      have h1 : IsMatching ({i} : Finset M) ({j} : Finset N) {(i, j)} := by
        refine ⟨by simp, ?_, ?_⟩ <;> simp
      have h2 := ag1171_le_worth a h1
      simp only [Finset.sum_singleton] at this h2
      linarith
  · rintro ⟨hdf, hsum⟩
    refine ⟨hsum, fun A B => ?_⟩
    apply ag1171_worth_le
    intro P hP
    exact ag1171_matching_sum_le a u v hdf hP

/-! ## Hall / Mendelsohn-Dulmage -/


open Classical in
/-- Mendelsohn–Dulmage type lemma from Hall. -/
theorem ag1171_md {M N : Type*} [Fintype M] [Fintype N] (E : M → N → Prop) (X : Finset M)
    (Y : Finset N)
    (hX : ∀ S ⊆ X, S.card ≤ (Finset.univ.filter (fun j => ∃ i ∈ S, E i j)).card)
    (hY : ∀ Q ⊆ Y, Q.card ≤ (Finset.univ.filter (fun i => ∃ j ∈ Q, E i j)).card) :
    ∃ P : Finset (M × N), (∀ p ∈ P, E p.1 p.2) ∧ (∀ p ∈ P, ∀ q ∈ P, p.1 = q.1 → p = q) ∧
      (∀ p ∈ P, ∀ q ∈ P, p.2 = q.2 → p = q) ∧ (∀ i ∈ X, ∃ p ∈ P, p.1 = i) ∧
      (∀ j ∈ Y, ∃ p ∈ P, p.2 = j) := by
  classical
  let Adj : M ⊕ N → N ⊕ M → Prop := fun x y =>
    match x, y with
    | Sum.inl i, Sum.inl j => E i j
    | Sum.inl i, Sum.inr i' => i' = i ∧ i ∉ X
    | Sum.inr j, Sum.inl j' => j' = j ∧ j ∉ Y
    | Sum.inr _, Sum.inr _ => True
  let t : M ⊕ N → Finset (N ⊕ M) := fun x => Finset.univ.filter (Adj x)
  have hmem : ∀ x y, y ∈ t x ↔ Adj x y := fun x y => by simp [t]
  have hall : ∀ s : Finset (M ⊕ N), s.card ≤ (s.biUnion t).card := by
    intro s
    have hcard := Finset.card_toLeft_add_card_toRight (u := s)
    have hS : ∀ i, i ∈ s.toLeft ↔ Sum.inl i ∈ s := fun i => Finset.mem_toLeft
    have hQ : ∀ j, j ∈ s.toRight ↔ Sum.inr j ∈ s := fun j => Finset.mem_toRight
    generalize s.toLeft = S at hcard hS
    generalize s.toRight = Q at hcard hQ
    by_cases hQe : Q = ∅
    · -- only sellers
      have hQc : Q.card = 0 := by rw [hQe]; rfl
      let S1 := S.filter (fun i => i ∈ X)
      let S2 := S.filter (fun i => i ∉ X)
      let Nb := Finset.univ.filter (fun j => ∃ i ∈ S1, E i j)
      have h1 : S1.card ≤ Nb.card := hX S1 (fun i hi => (Finset.mem_filter.1 hi).2)
      have hsplit : S1.card + S2.card = S.card := Finset.card_filter_add_card_filter_not _
      have hsub : Nb.map Function.Embedding.inl ∪ S2.map Function.Embedding.inr ⊆ s.biUnion t := by
        intro y hy
        rcases Finset.mem_union.1 hy with hy | hy
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hy
          obtain ⟨i, hi, hij⟩ := (Finset.mem_filter.1 hj).2
          have hi' := (Finset.mem_filter.1 hi)
          refine Finset.mem_biUnion.2 ⟨Sum.inl i, ?_, ?_⟩
          · exact (hS i).1 hi'.1
          · rw [hmem]; exact hij
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hy
          have hi' := (Finset.mem_filter.1 hi)
          refine Finset.mem_biUnion.2 ⟨Sum.inl i, ?_, ?_⟩
          · exact (hS i).1 hi'.1
          · rw [hmem]; exact ⟨rfl, hi'.2⟩
      have hdisj : Disjoint (Nb.map Function.Embedding.inl) (S2.map Function.Embedding.inr) := by
        rw [Finset.disjoint_left]
        intro y hy hy'
        obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hy
        obtain ⟨i, _, hh⟩ := Finset.mem_map.1 hy'
        exact Sum.inr_ne_inl hh
      have hc := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map] at hc
      omega
    · -- some dummy seller present
      obtain ⟨j0, hj0⟩ := Finset.nonempty_iff_ne_empty.2 hQe
      let NS := Finset.univ.filter (fun j => ∃ i ∈ S, E i j)
      let U := NS ∪ Q.filter (fun j => j ∉ Y)
      let Q1 := Q.filter (fun j => j ∈ Y ∧ j ∉ NS)
      let NQ := Finset.univ.filter (fun i => ∃ j ∈ Q1, E i j)
      have h1 : Q1.card ≤ NQ.card := hY Q1 (fun j hj => (Finset.mem_filter.1 hj).2.1)
      have hdisj0 : Disjoint S NQ := by
        rw [Finset.disjoint_left]
        intro i hi hi'
        obtain ⟨j, hj, hij⟩ := (Finset.mem_filter.1 hi').2
        have hj' := (Finset.mem_filter.1 hj).2
        apply hj'.2
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hi, hij⟩
      have h2 : S.card + NQ.card ≤ Fintype.card M := by
        rw [← Finset.card_union_of_disjoint hdisj0]
        exact Finset.card_le_univ _
      have hQsub : Q ⊆ Q1 ∪ U := by
        intro j hj
        by_cases hY' : j ∈ Y
        · by_cases hNS : j ∈ NS
          · exact Finset.mem_union.2 (Or.inr (Finset.mem_union.2 (Or.inl hNS)))
          · exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨hj, hY', hNS⟩))
        · exact Finset.mem_union.2 (Or.inr (Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨hj, hY'⟩))))
      have h3 : Q.card ≤ Q1.card + U.card :=
        (Finset.card_le_card hQsub).trans (Finset.card_union_le _ _)
      have hsub : (Finset.univ : Finset M).map Function.Embedding.inr ∪ U.map Function.Embedding.inl ⊆
          s.biUnion t := by
        intro y hy
        rcases Finset.mem_union.1 hy with hy | hy
        · obtain ⟨i, _, rfl⟩ := Finset.mem_map.1 hy
          refine Finset.mem_biUnion.2 ⟨Sum.inr j0, ?_, ?_⟩
          · exact (hQ j0).1 hj0
          · rw [hmem]; trivial
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hy
          rcases Finset.mem_union.1 hj with hj | hj
          · obtain ⟨i, hi, hij⟩ := (Finset.mem_filter.1 hj).2
            refine Finset.mem_biUnion.2 ⟨Sum.inl i, ?_, ?_⟩
            · exact (hS i).1 hi
            · rw [hmem]; exact hij
          · have hj' := Finset.mem_filter.1 hj
            refine Finset.mem_biUnion.2 ⟨Sum.inr j, ?_, ?_⟩
            · exact (hQ j).1 hj'.1
            · rw [hmem]; exact ⟨rfl, hj'.2⟩
      have hdisj : Disjoint ((Finset.univ : Finset M).map Function.Embedding.inr)
          (U.map Function.Embedding.inl) := by
        rw [Finset.disjoint_left]
        intro y hy hy'
        obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hy'
        obtain ⟨i, _, hh⟩ := Finset.mem_map.1 hy
        exact Sum.inr_ne_inl hh
      have hc := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map,
        Finset.card_univ] at hc
      omega
  obtain ⟨f, hfinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have hfbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hfinj, ?_⟩
    simp [Fintype.card_sum, add_comm]
  refine ⟨Finset.univ.filter (fun p : M × N => f (Sum.inl p.1) = Sum.inl p.2), ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have h1 := (Finset.mem_filter.1 hp).2
    have h2 := (hmem _ _).1 (hf (Sum.inl p.1))
    rw [h1] at h2
    exact h2
  · intro p hp q hq hpq
    have h1 := (Finset.mem_filter.1 hp).2
    have h2 := (Finset.mem_filter.1 hq).2
    rw [hpq] at h1
    rw [h1] at h2
    exact Prod.ext hpq (Sum.inl_injective h2)
  · intro p hp q hq hpq
    have h1 := (Finset.mem_filter.1 hp).2
    have h2 := (Finset.mem_filter.1 hq).2
    have := hfinj (h1.trans ((congrArg Sum.inl hpq).trans h2.symm))
    exact Prod.ext (Sum.inl_injective this) hpq
  · intro i hi
    have h2 := (hmem _ _).1 (hf (Sum.inl i))
    rcases hfi : f (Sum.inl i) with j | i'
    · exact ⟨(i, j), Finset.mem_filter.2 ⟨Finset.mem_univ _, hfi⟩, rfl⟩
    · rw [hfi] at h2
      exact absurd hi h2.2
  · intro j hj
    obtain ⟨x, hx⟩ := hfbij.2 (Sum.inl j)
    rcases x with i | j'
    · exact ⟨(i, j), Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩, rfl⟩
    · have h2 := (hmem _ _).1 (hf (Sum.inr j'))
      rw [hx] at h2
      have : j = j' := h2.1
      subst this
      exact absurd hj h2.2

/-! ## Perturbation -/

open Classical in
/-- Perturbation: a dual-optimal vector has the Hall property on the positive sellers. -/
theorem ag1171_hall_side {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ) (u : M → ℝ)
    (v : N → ℝ) (hdf : ag1171_DF a u v)
    (hmin : ∀ (u' : M → ℝ) (v' : N → ℝ), ag1171_DF a u' v' →
      ∑ i, u i + ∑ j, v j ≤ ∑ i, u' i + ∑ j, v' j)
    (S : Finset M) (hS : ∀ i ∈ S, 0 < u i) :
    S.card ≤ (Finset.univ.filter (fun j => ∃ i ∈ S, u i + v j = a i j)).card := by
  by_contra hlt
  rw [not_le] at hlt
  set Nb := Finset.univ.filter (fun j => ∃ i ∈ S, u i + v j = a i j) with hNb
  have hne : (S ×ˢ (Finset.univ : Finset (Option N))).Nonempty := by
    have : 0 < S.card := lt_of_le_of_lt (Nat.zero_le _) hlt
    obtain ⟨i, hi⟩ := Finset.card_pos.1 this
    exact ⟨(i, none), Finset.mem_product.2 ⟨hi, Finset.mem_univ _⟩⟩
  let g : M × Option N → ℝ := fun x =>
    match x.2 with
    | none => u x.1
    | some j => if j ∈ Nb then u x.1 else u x.1 + v j - a x.1 j
  obtain ⟨x0, hx0, hmin0⟩ := Finset.exists_min_image (S ×ˢ (Finset.univ : Finset (Option N))) g hne
  set ε := g x0 with hε
  have hslack : ∀ i ∈ S, ∀ j, j ∉ Nb → 0 < u i + v j - a i j := by
    intro i hi j hj
    have h1 := hdf.2.2 i j
    have h2 : u i + v j ≠ a i j := fun h => hj (Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hi, h⟩)
    have := lt_of_le_of_ne h1 (Ne.symm h2)
    linarith
  have hεpos : 0 < ε := by
    obtain ⟨i0, j0⟩ := x0
    have hi0 : i0 ∈ S := (Finset.mem_product.1 hx0).1
    rw [hε]
    rcases j0 with _ | j0
    · exact hS i0 hi0
    · simp only [g]
      split_ifs with h
      · exact hS i0 hi0
      · exact hslack i0 hi0 j0 h
  have hε1 : ∀ i ∈ S, ε ≤ u i := by
    intro i hi
    exact hmin0 (i, none) (Finset.mem_product.2 ⟨hi, Finset.mem_univ _⟩)
  have hε2 : ∀ i ∈ S, ∀ j, j ∉ Nb → ε ≤ u i + v j - a i j := by
    intro i hi j hj
    have := hmin0 (i, some j) (Finset.mem_product.2 ⟨hi, Finset.mem_univ _⟩)
    simpa [g, hj] using this
  let u' : M → ℝ := fun i => u i - if i ∈ S then ε else 0
  let v' : N → ℝ := fun j => v j + if j ∈ Nb then ε else 0
  have hdf' : ag1171_DF a u' v' := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simp only [u']
      split_ifs with h
      · linarith [hε1 i h]
      · linarith [hdf.1 i]
    · intro j
      simp only [v']
      split_ifs
      · linarith [hdf.2.1 j]
      · linarith [hdf.2.1 j]
    · intro i j
      simp only [u', v']
      have hab := hdf.2.2 i j
      by_cases hi : i ∈ S
      · by_cases hj : j ∈ Nb
        · simp only [hi, hj, if_true]; linarith
        · have := hε2 i hi j hj
          simp only [hi, hj, if_true, if_false]; linarith
      · by_cases hj : j ∈ Nb
        · simp only [hi, hj, if_true, if_false]; linarith
        · simp only [hi, hj, if_false]; linarith
  have hobj := hmin u' v' hdf'
  have e1 : ∑ i, u' i = ∑ i, u i - ε * S.card := by
    simp only [u']
    rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul]
    ring
  have e2 : ∑ j, v' j = ∑ j, v j + ε * Nb.card := by
    simp only [v']
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul]
    ring
  rw [e1, e2] at hobj
  have hlt' : (Nb.card : ℝ) < S.card := by exact_mod_cast hlt
  nlinarith

/-! ## Existence of a dual optimum -/

theorem ag1171_exists_min {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) :
    ∃ (u : M → ℝ) (v : N → ℝ), ag1171_DF a u v ∧
      ∀ (u' : M → ℝ) (v' : N → ℝ), ag1171_DF a u' v' →
        ∑ i, u i + ∑ j, v j ≤ ∑ i, u' i + ∑ j, v' j := by
  classical
  let obj : (M → ℝ) × (N → ℝ) → ℝ := fun p => ∑ i, p.1 i + ∑ j, p.2 j
  have hobj : Continuous obj := by
    simp only [obj]; fun_prop
  let p0 : (M → ℝ) × (N → ℝ) := (fun i => ∑ j, a i j, fun _ => 0)
  have hp0 : ag1171_DF a p0.1 p0.2 := by
    refine ⟨fun i => Finset.sum_nonneg (fun j _ => ha i j), fun _ => le_rfl, fun i j => ?_⟩
    simp only [p0, add_zero]
    exact Finset.single_le_sum (f := fun j => a i j) (fun j _ => ha i j) (Finset.mem_univ j)
  set C := obj p0 with hC
  let K : Set ((M → ℝ) × (N → ℝ)) := {p | ag1171_DF a p.1 p.2 ∧ obj p ≤ C}
  have hKc : IsCompact K := by
    have hbox : IsCompact ((Set.univ.pi fun _ : M => Set.Icc (0:ℝ) C) ×ˢ
        (Set.univ.pi fun _ : N => Set.Icc (0:ℝ) C)) :=
      (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
    refine hbox.of_isClosed_subset ?_ ?_
    · have c1 : IsClosed {p : (M → ℝ) × (N → ℝ) | ∀ i, 0 ≤ p.1 i} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
      have c2 : IsClosed {p : (M → ℝ) × (N → ℝ) | ∀ j, 0 ≤ p.2 j} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun j => isClosed_le continuous_const (by fun_prop)
      have c3 : IsClosed {p : (M → ℝ) × (N → ℝ) | ∀ i j, a i j ≤ p.1 i + p.2 j} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun i => isClosed_iInter fun j =>
          isClosed_le continuous_const (by fun_prop)
      have c4 : IsClosed {p : (M → ℝ) × (N → ℝ) | obj p ≤ C} :=
        isClosed_le hobj continuous_const
      have e : K = (({p : (M → ℝ) × (N → ℝ) | ∀ i, 0 ≤ p.1 i} ∩ {p | ∀ j, 0 ≤ p.2 j}) ∩
          {p | ∀ i j, a i j ≤ p.1 i + p.2 j}) ∩ {p | obj p ≤ C} := by
        ext p
        simp only [K, ag1171_DF, Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
      rw [e]
      exact ((c1.inter c2).inter c3).inter c4
    · intro p hp
      obtain ⟨⟨hu, hv, -⟩, hle⟩ := hp
      have h2 : 0 ≤ ∑ k, p.2 k := Finset.sum_nonneg (fun k _ => hv k)
      have h2' : 0 ≤ ∑ k, p.1 k := Finset.sum_nonneg (fun k _ => hu k)
      have hop : obj p = ∑ i, p.1 i + ∑ j, p.2 j := rfl
      refine ⟨fun i _ => ⟨hu i, ?_⟩, fun j _ => ⟨hv j, ?_⟩⟩
      · have h1 : p.1 i ≤ ∑ k, p.1 k :=
          Finset.single_le_sum (f := fun k => p.1 k) (fun k _ => hu k) (Finset.mem_univ i)
        linarith
      · have h1 : p.2 j ≤ ∑ k, p.2 k :=
          Finset.single_le_sum (f := fun k => p.2 k) (fun k _ => hv k) (Finset.mem_univ j)
        linarith
  obtain ⟨p, hpK, hpmin⟩ := hKc.exists_isMinOn ⟨p0, hp0, le_rfl⟩ hobj.continuousOn
  refine ⟨p.1, p.2, hpK.1, fun u' v' hq => ?_⟩
  by_cases hqC : obj (u', v') ≤ C
  · exact isMinOn_iff.1 hpmin (u', v') (show (u', v') ∈ K from ⟨hq, hqC⟩)
  · have h1 := hpK.2
    have h2 := not_le.1 hqC
    show obj p ≤ obj (u', v')
    linarith

/-! ## Nonemptiness of the core (Egerváry) -/

open AssignmentGame.CoreCorners in
theorem ag1171_core_nonempty {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) : ∃ (u : M → ℝ) (v : N → ℝ), (u, v) ∈ core a := by
  classical
  obtain ⟨u, v, hdf, hmin⟩ := ag1171_exists_min a ha
  have hX : ∀ S ⊆ (Finset.univ.filter (fun i => 0 < u i)), S.card ≤
      (Finset.univ.filter (fun j => ∃ i ∈ S, (fun i j => u i + v j = a i j) i j)).card := by
    intro S hS
    convert ag1171_hall_side a u v hdf hmin S (fun i hi => (Finset.mem_filter.1 (hS hi)).2)
      using 3
  have hY : ∀ Q ⊆ (Finset.univ.filter (fun j => 0 < v j)), Q.card ≤
      (Finset.univ.filter (fun i => ∃ j ∈ Q, (fun i j => u i + v j = a i j) i j)).card := by
    intro Q hQ
    have hdf' : ag1171_DF (fun j i => a i j) v u :=
      ⟨hdf.2.1, hdf.1, fun j i => by have := hdf.2.2 i j; linarith⟩
    have hmin' : ∀ (v' : N → ℝ) (u' : M → ℝ), ag1171_DF (fun j i => a i j) v' u' →
        ∑ j, v j + ∑ i, u i ≤ ∑ j, v' j + ∑ i, u' i := by
      intro v' u' h
      have := hmin u' v' ⟨h.2.1, h.1, fun i j => by have := h.2.2 j i; linarith⟩
      linarith
    convert ag1171_hall_side (fun j i => a i j) v u hdf' hmin' Q
      (fun j hj => (Finset.mem_filter.1 (hQ hj)).2) using 3
    simp only [add_comm]
  obtain ⟨P, hE, h1, h2, hcx, hcy⟩ := ag1171_md (fun i j => u i + v j = a i j) _ _ hX hY
  have hP : IsMatching (Finset.univ : Finset M) (Finset.univ : Finset N) P :=
    ⟨fun p _ => Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h1, h2⟩
  have hsumu : ∑ i, u i = ∑ i ∈ P.image Prod.fst, u i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    by_contra hne
    have : 0 < u i := lt_of_le_of_ne (hdf.1 i) (Ne.symm hne)
    obtain ⟨p, hp, hp1⟩ := hcx i (Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩)
    exact hi (Finset.mem_image.2 ⟨p, hp, hp1⟩)
  have hsumv : ∑ j, v j = ∑ j ∈ P.image Prod.snd, v j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    by_contra hne
    have : 0 < v j := lt_of_le_of_ne (hdf.2.1 j) (Ne.symm hne)
    obtain ⟨p, hp, hp1⟩ := hcy j (Finset.mem_filter.2 ⟨Finset.mem_univ _, this⟩)
    exact hj (Finset.mem_image.2 ⟨p, hp, hp1⟩)
  have e1 : ∑ p ∈ P, u p.1 = ∑ i ∈ P.image Prod.fst, u i := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact h1 p hp q hq hpq
  have e2 : ∑ p ∈ P, v p.2 = ∑ j ∈ P.image Prod.snd, v j := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact h2 p hp q hq hpq
  have hPsum : ∑ p ∈ P, a p.1 p.2 = ∑ i, u i + ∑ j, v j := by
    calc ∑ p ∈ P, a p.1 p.2 = ∑ p ∈ P, (u p.1 + v p.2) :=
          Finset.sum_congr rfl fun p hp => (hE p hp).symm
      _ = ∑ p ∈ P, u p.1 + ∑ p ∈ P, v p.2 := Finset.sum_add_distrib
      _ = ∑ i, u i + ∑ j, v j := by rw [e1, e2, hsumu, hsumv]
  have hge : ∑ i, u i + ∑ j, v j ≤ worth a Finset.univ Finset.univ := by
    rw [← hPsum]; exact ag1171_le_worth a hP
  have hle : worth a Finset.univ Finset.univ ≤ ∑ i, u i + ∑ j, v j := by
    apply ag1171_worth_le
    intro P' hP'
    exact ag1171_matching_sum_le a u v hdf hP'
  exact ⟨u, v, (ag1171_core_iff a u v).2 ⟨hdf, le_antisymm hge hle⟩⟩

/-! ## Lattice structure of the core -/

open AssignmentGame.CoreCorners in
theorem ag1171_cs {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ) {u : M → ℝ} {v : N → ℝ}
    (h : (u, v) ∈ core a) {P : Finset (M × N)}
    (hP : IsMatching (Finset.univ : Finset M) (Finset.univ : Finset N) P)
    (hw : worth a Finset.univ Finset.univ = ∑ p ∈ P, a p.1 p.2) :
    (∀ p ∈ P, u p.1 + v p.2 = a p.1 p.2) ∧ (∀ i, (∀ p ∈ P, p.1 ≠ i) → u i = 0) ∧
      (∀ j, (∀ p ∈ P, p.2 ≠ j) → v j = 0) := by
  classical
  obtain ⟨⟨hu, hv, hab⟩, hsum⟩ := (ag1171_core_iff a u v).1 h
  obtain ⟨-, h1, h2⟩ := hP
  have e1 : ∑ p ∈ P, u p.1 = ∑ i ∈ P.image Prod.fst, u i := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact h1 p hp q hq hpq
  have e2 : ∑ p ∈ P, v p.2 = ∑ j ∈ P.image Prod.snd, v j := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact h2 p hp q hq hpq
  have hF' : ∑ i ∈ P.image Prod.fst, u i + ∑ i ∈ (P.image Prod.fst)ᶜ, u i = ∑ i, u i :=
    Finset.sum_add_sum_compl _ u
  have hG' : ∑ j ∈ P.image Prod.snd, v j + ∑ j ∈ (P.image Prod.snd)ᶜ, v j = ∑ j, v j :=
    Finset.sum_add_sum_compl _ v
  have hT2 : 0 ≤ ∑ i ∈ (P.image Prod.fst)ᶜ, u i := Finset.sum_nonneg fun i _ => hu i
  have hT3 : 0 ≤ ∑ j ∈ (P.image Prod.snd)ᶜ, v j := Finset.sum_nonneg fun j _ => hv j
  have hT1 : 0 ≤ ∑ p ∈ P, (u p.1 + v p.2 - a p.1 p.2) :=
    Finset.sum_nonneg fun p _ => by linarith [hab p.1 p.2]
  have hexp : ∑ p ∈ P, (u p.1 + v p.2 - a p.1 p.2) =
      ∑ p ∈ P, u p.1 + ∑ p ∈ P, v p.2 - ∑ p ∈ P, a p.1 p.2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hz1 : ∑ p ∈ P, (u p.1 + v p.2 - a p.1 p.2) = 0 := by linarith
  have hz2 : ∑ i ∈ (P.image Prod.fst)ᶜ, u i = 0 := by linarith
  have hz3 : ∑ j ∈ (P.image Prod.snd)ᶜ, v j = 0 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun p _ => by linarith [hab p.1 p.2])).1 hz1 p hp
    linarith
  · intro i hi
    have hiF : i ∈ (P.image Prod.fst)ᶜ := by
      rw [Finset.mem_compl, Finset.mem_image]
      rintro ⟨p, hp, hp1⟩
      exact hi p hp hp1
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hu i)).1 hz2 i hiF
  · intro j hj
    have hjG : j ∈ (P.image Prod.snd)ᶜ := by
      rw [Finset.mem_compl, Finset.mem_image]
      rintro ⟨p, hp, hp1⟩
      exact hj p hp hp1
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hv j)).1 hz3 j hjG

open AssignmentGame.CoreCorners in
theorem ag1171_sum_of_cs {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ) (u : M → ℝ)
    (v : N → ℝ) {P : Finset (M × N)}
    (hP : IsMatching (Finset.univ : Finset M) (Finset.univ : Finset N) P)
    (h1 : ∀ p ∈ P, u p.1 + v p.2 = a p.1 p.2) (h2 : ∀ i, (∀ p ∈ P, p.1 ≠ i) → u i = 0)
    (h3 : ∀ j, (∀ p ∈ P, p.2 ≠ j) → v j = 0) :
    ∑ i, u i + ∑ j, v j = ∑ p ∈ P, a p.1 p.2 := by
  classical
  obtain ⟨-, hi1, hi2⟩ := hP
  have hsumu : ∑ i, u i = ∑ i ∈ P.image Prod.fst, u i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    exact h2 i (fun p hp hp1 => hi (Finset.mem_image.2 ⟨p, hp, hp1⟩))
  have hsumv : ∑ j, v j = ∑ j ∈ P.image Prod.snd, v j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    exact h3 j (fun p hp hp1 => hj (Finset.mem_image.2 ⟨p, hp, hp1⟩))
  have e1 : ∑ p ∈ P, u p.1 = ∑ i ∈ P.image Prod.fst, u i := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact hi1 p hp q hq hpq
  have e2 : ∑ p ∈ P, v p.2 = ∑ j ∈ P.image Prod.snd, v j := by
    rw [Finset.sum_image]
    intro p hp q hq hpq
    exact hi2 p hp q hq hpq
  calc ∑ i, u i + ∑ j, v j = ∑ p ∈ P, u p.1 + ∑ p ∈ P, v p.2 := by
        rw [e1, e2, hsumu, hsumv]
    _ = ∑ p ∈ P, (u p.1 + v p.2) := Finset.sum_add_distrib.symm
    _ = ∑ p ∈ P, a p.1 p.2 := Finset.sum_congr rfl h1

open AssignmentGame.CoreCorners in
theorem ag1171_core_lattice {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    {u u' : M → ℝ} {v v' : N → ℝ} (h : (u, v) ∈ core a) (h' : (u', v') ∈ core a) :
    ((fun i => max (u i) (u' i), fun j => min (v j) (v' j)) ∈ core a) ∧
    ((fun i => min (u i) (u' i), fun j => max (v j) (v' j)) ∈ core a) := by
  classical
  obtain ⟨P, hP, hw⟩ := ag1171_exists_opt a Finset.univ Finset.univ
  obtain ⟨c1, c2, c3⟩ := ag1171_cs a h hP hw
  obtain ⟨c1', c2', c3'⟩ := ag1171_cs a h' hP hw
  obtain ⟨⟨hu, hv, hab⟩, -⟩ := (ag1171_core_iff a u v).1 h
  obtain ⟨⟨hu', hv', hab'⟩, -⟩ := (ag1171_core_iff a u' v').1 h'
  constructor
  · rw [ag1171_core_iff]
    have hdf : ag1171_DF a (fun i => max (u i) (u' i)) (fun j => min (v j) (v' j)) := by
      refine ⟨fun i => le_max_of_le_left (hu i), fun j => le_min (hv j) (hv' j), fun i j => ?_⟩
      rcases le_total (v j) (v' j) with hj | hj
      · show a i j ≤ max (u i) (u' i) + min (v j) (v' j)
        rw [min_eq_left hj]; linarith [le_max_left (u i) (u' i), hab i j]
      · show a i j ≤ max (u i) (u' i) + min (v j) (v' j)
        rw [min_eq_right hj]; linarith [le_max_right (u i) (u' i), hab' i j]
    refine ⟨hdf, ?_⟩
    rw [hw]
    refine ag1171_sum_of_cs a _ _ hP ?_ ?_ ?_
    · intro p hp
      have e1 := c1 p hp
      have e2 := c1' p hp
      show max (u p.1) (u' p.1) + min (v p.2) (v' p.2) = a p.1 p.2
      rcases le_total (u p.1) (u' p.1) with hh | hh
      · rw [max_eq_right hh, min_eq_right (by linarith)]; linarith
      · rw [max_eq_left hh, min_eq_left (by linarith)]; linarith
    · intro i hi
      show max (u i) (u' i) = 0
      rw [c2 i hi, c2' i hi]; simp
    · intro j hj
      show min (v j) (v' j) = 0
      rw [c3 j hj, c3' j hj]; simp
  · rw [ag1171_core_iff]
    have hdf : ag1171_DF a (fun i => min (u i) (u' i)) (fun j => max (v j) (v' j)) := by
      refine ⟨fun i => le_min (hu i) (hu' i), fun j => le_max_of_le_left (hv j), fun i j => ?_⟩
      rcases le_total (u i) (u' i) with hj | hj
      · show a i j ≤ min (u i) (u' i) + max (v j) (v' j)
        rw [min_eq_left hj]; linarith [le_max_left (v j) (v' j), hab i j]
      · show a i j ≤ min (u i) (u' i) + max (v j) (v' j)
        rw [min_eq_right hj]; linarith [le_max_right (v j) (v' j), hab' i j]
    refine ⟨hdf, ?_⟩
    rw [hw]
    refine ag1171_sum_of_cs a _ _ hP ?_ ?_ ?_
    · intro p hp
      have e1 := c1 p hp
      have e2 := c1' p hp
      show min (u p.1) (u' p.1) + max (v p.2) (v' p.2) = a p.1 p.2
      rcases le_total (u p.1) (u' p.1) with hh | hh
      · rw [min_eq_left hh, max_eq_left (by linarith)]; linarith
      · rw [min_eq_right hh, max_eq_right (by linarith)]; linarith
    · intro i hi
      show min (u i) (u' i) = 0
      rw [c2 i hi, c2' i hi]; simp
    · intro j hj
      show max (v j) (v' j) = 0
      rw [c3 j hj, c3' j hj]; simp

/-! ## Compactness and attainment of the extrema -/

open AssignmentGame.CoreCorners in
theorem ag1171_core_compact {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ) :
    IsCompact (core a) := by
  classical
  set W := worth a Finset.univ Finset.univ with hW
  have hbox : IsCompact ((Set.univ.pi fun _ : M => Set.Icc (0:ℝ) W) ×ˢ
      (Set.univ.pi fun _ : N => Set.Icc (0:ℝ) W)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  refine hbox.of_isClosed_subset ?_ ?_
  · have c1 : IsClosed {p : (M → ℝ) × (N → ℝ) | ∑ i, p.1 i + ∑ j, p.2 j = W} :=
      isClosed_eq (by fun_prop) continuous_const
    have c2 : IsClosed {p : (M → ℝ) × (N → ℝ) | ∀ (A : Finset M) (B : Finset N),
        worth a A B ≤ ∑ i ∈ A, p.1 i + ∑ j ∈ B, p.2 j} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun A => isClosed_iInter fun B =>
        isClosed_le continuous_const (by fun_prop)
    exact c1.inter c2
  · intro p hp
    have hp' : (p.1, p.2) ∈ core a := by rwa [Prod.mk.eta]
    obtain ⟨⟨hu, hv, -⟩, hsum⟩ := (ag1171_core_iff a p.1 p.2).1 hp'
    have h2 : 0 ≤ ∑ k, p.2 k := Finset.sum_nonneg (fun k _ => hv k)
    have h2' : 0 ≤ ∑ k, p.1 k := Finset.sum_nonneg (fun k _ => hu k)
    refine ⟨fun i _ => ⟨hu i, ?_⟩, fun j _ => ⟨hv j, ?_⟩⟩
    · have h1 : p.1 i ≤ ∑ k, p.1 k :=
        Finset.single_le_sum (f := fun k => p.1 k) (fun k _ => hu k) (Finset.mem_univ i)
      linarith
    · have h1 : p.2 j ≤ ∑ k, p.2 k :=
        Finset.single_le_sum (f := fun k => p.2 k) (fun k _ => hv k) (Finset.mem_univ j)
      linarith

open AssignmentGame.CoreCorners in
theorem ag1171_ext {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (h0 : (core a).Nonempty) (f : (M → ℝ) × (N → ℝ) → ℝ) (hf : Continuous f) :
    (∃ p ∈ core a, ∀ q ∈ core a, f p ≤ f q) ∧ (∃ p ∈ core a, ∀ q ∈ core a, f q ≤ f p) := by
  obtain ⟨p, hp, hpm⟩ := (ag1171_core_compact a).exists_isMinOn h0 hf.continuousOn
  obtain ⟨p', hp', hpM⟩ := (ag1171_core_compact a).exists_isMaxOn h0 hf.continuousOn
  exact ⟨⟨p, hp, fun q hq => isMinOn_iff.1 hpm q hq⟩, ⟨p', hp', fun q hq => isMaxOn_iff.1 hpM q hq⟩⟩

open AssignmentGame.CoreCorners in
theorem ag1171_uLo {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (h0 : (core a).Nonempty) (i : M) :
    ∃ p ∈ core a, p.1 i = uLo a i ∧ ∀ q ∈ core a, uLo a i ≤ q.1 i := by
  obtain ⟨⟨p, hp, hpm⟩, -⟩ := ag1171_ext a h0 (fun p => p.1 i) (by fun_prop)
  have : uLo a i = p.1 i := by
    unfold uLo
    exact IsLeast.csInf_eq ⟨⟨p, hp, rfl⟩, by rintro _ ⟨q, hq, rfl⟩; exact hpm q hq⟩
  exact ⟨p, hp, this.symm, fun q hq => this ▸ hpm q hq⟩

open AssignmentGame.CoreCorners in
theorem ag1171_uHi {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (h0 : (core a).Nonempty) (i : M) :
    ∃ p ∈ core a, p.1 i = uHi a i ∧ ∀ q ∈ core a, q.1 i ≤ uHi a i := by
  obtain ⟨-, ⟨p, hp, hpm⟩⟩ := ag1171_ext a h0 (fun p => p.1 i) (by fun_prop)
  have : uHi a i = p.1 i := by
    unfold uHi
    exact IsGreatest.csSup_eq ⟨⟨p, hp, rfl⟩, by rintro _ ⟨q, hq, rfl⟩; exact hpm q hq⟩
  exact ⟨p, hp, this.symm, fun q hq => this ▸ hpm q hq⟩

open AssignmentGame.CoreCorners in
theorem ag1171_vLo {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (h0 : (core a).Nonempty) (j : N) :
    ∃ p ∈ core a, p.2 j = vLo a j ∧ ∀ q ∈ core a, vLo a j ≤ q.2 j := by
  obtain ⟨⟨p, hp, hpm⟩, -⟩ := ag1171_ext a h0 (fun p => p.2 j) (by fun_prop)
  have : vLo a j = p.2 j := by
    unfold vLo
    exact IsLeast.csInf_eq ⟨⟨p, hp, rfl⟩, by rintro _ ⟨q, hq, rfl⟩; exact hpm q hq⟩
  exact ⟨p, hp, this.symm, fun q hq => this ▸ hpm q hq⟩

open AssignmentGame.CoreCorners in
theorem ag1171_vHi {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (h0 : (core a).Nonempty) (j : N) :
    ∃ p ∈ core a, p.2 j = vHi a j ∧ ∀ q ∈ core a, q.2 j ≤ vHi a j := by
  obtain ⟨-, ⟨p, hp, hpm⟩⟩ := ag1171_ext a h0 (fun p => p.2 j) (by fun_prop)
  have : vHi a j = p.2 j := by
    unfold vHi
    exact IsGreatest.csSup_eq ⟨⟨p, hp, rfl⟩, by rintro _ ⟨q, hq, rfl⟩; exact hpm q hq⟩
  exact ⟨p, hp, this.symm, fun q hq => this ▸ hpm q hq⟩

/-! ## Finite meets and joins -/

open AssignmentGame.CoreCorners in
theorem ag1171_meet {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (h0 : (core a).Nonempty) {ι : Type*} [Fintype ι] (p : ι → (M → ℝ) × (N → ℝ))
    (hp : ∀ k, p k ∈ core a) :
    ∃ r ∈ core a, ∀ k, (∀ i, r.1 i ≤ (p k).1 i) ∧ (∀ j, (p k).2 j ≤ r.2 j) := by
  classical
  have key : ∀ s : Finset ι, ∃ r ∈ core a, ∀ k ∈ s,
      (∀ i, r.1 i ≤ (p k).1 i) ∧ (∀ j, (p k).2 j ≤ r.2 j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => obtain ⟨r, hr⟩ := h0; exact ⟨r, hr, by simp⟩
    | insert k s hk ih =>
      obtain ⟨r, hr, hrs⟩ := ih
      have hr' : (r.1, r.2) ∈ core a := by rwa [Prod.mk.eta]
      have hk' : ((p k).1, (p k).2) ∈ core a := by rw [Prod.mk.eta]; exact hp k
      have := (ag1171_core_lattice a hr' hk').2
      refine ⟨(fun i => min (r.1 i) ((p k).1 i), fun j => max (r.2 j) ((p k).2 j)), this, ?_⟩
      intro k' hk''
      rcases Finset.mem_insert.1 hk'' with rfl | hk''
      · exact ⟨fun i => min_le_right _ _, fun j => le_max_right _ _⟩
      · obtain ⟨h1, h2⟩ := hrs k' hk''
        exact ⟨fun i => (min_le_left _ _).trans (h1 i), fun j => (h2 j).trans (le_max_left _ _)⟩
  obtain ⟨r, hr, h⟩ := key Finset.univ
  exact ⟨r, hr, fun k => h k (Finset.mem_univ k)⟩

open AssignmentGame.CoreCorners in
theorem ag1171_join {M N : Type*} [Fintype M] [Fintype N] (a : M → N → ℝ)
    (h0 : (core a).Nonempty) {ι : Type*} [Fintype ι] (p : ι → (M → ℝ) × (N → ℝ))
    (hp : ∀ k, p k ∈ core a) :
    ∃ r ∈ core a, ∀ k, (∀ i, (p k).1 i ≤ r.1 i) ∧ (∀ j, r.2 j ≤ (p k).2 j) := by
  classical
  have key : ∀ s : Finset ι, ∃ r ∈ core a, ∀ k ∈ s,
      (∀ i, (p k).1 i ≤ r.1 i) ∧ (∀ j, r.2 j ≤ (p k).2 j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => obtain ⟨r, hr⟩ := h0; exact ⟨r, hr, by simp⟩
    | insert k s hk ih =>
      obtain ⟨r, hr, hrs⟩ := ih
      have hr' : (r.1, r.2) ∈ core a := by rwa [Prod.mk.eta]
      have hk' : ((p k).1, (p k).2) ∈ core a := by rw [Prod.mk.eta]; exact hp k
      have := (ag1171_core_lattice a hr' hk').1
      refine ⟨(fun i => max (r.1 i) ((p k).1 i), fun j => min (r.2 j) ((p k).2 j)), this, ?_⟩
      intro k' hk''
      rcases Finset.mem_insert.1 hk'' with rfl | hk''
      · exact ⟨fun i => le_max_right _ _, fun j => min_le_right _ _⟩
      · obtain ⟨h1, h2⟩ := hrs k' hk''
        exact ⟨fun i => (h1 i).trans (le_max_left _ _), fun j => (min_le_left _ _).trans (h2 j)⟩
  obtain ⟨r, hr, h⟩ := key Finset.univ
  exact ⟨r, hr, fun k => h k (Finset.mem_univ k)⟩

/-! ## The theorem -/

open Finset AssignmentGame.CoreCorners in
theorem core_corners_accepted {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j) :
    (uLo a, vHi a) ∈ core a ∧ (uHi a, vLo a) ∈ core a ∧
    ∀ (u' u'' : M → ℝ) (v' v'' : N → ℝ), (u', v') ∈ core a → (u'', v'') ∈ core a →
      ∑ i, (u' i - u'' i) ^ 2 + ∑ j, (v' j - v'' j) ^ 2 ≤
        ∑ i, (uLo a i - uHi a i) ^ 2 + ∑ j, (vHi a j - vLo a j) ^ 2 := by
  classical
  obtain ⟨u0, v0, h0⟩ := ag1171_core_nonempty a ha
  have hne : (core a).Nonempty := ⟨(u0, v0), h0⟩
  choose pl hpl using fun i => ag1171_uLo a hne i
  choose ph hph using fun i => ag1171_uHi a hne i
  choose ql hql using fun j => ag1171_vLo a hne j
  choose qh hqh using fun j => ag1171_vHi a hne j
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨r, hr, hrk⟩ := ag1171_meet a hne (ι := M ⊕ N) (Sum.elim pl qh) (by
      intro k
      rcases k with i | j
      · exact (hpl i).1
      · exact (hqh j).1)
    have hru : ∀ i, r.1 i = uLo a i := by
      intro i
      apply le_antisymm
      · have := (hrk (Sum.inl i)).1 i
        simpa [(hpl i).2.1] using this
      · exact (hpl i).2.2 r hr
    have hrv : ∀ j, r.2 j = vHi a j := by
      intro j
      apply le_antisymm
      · exact (hqh j).2.2 r hr
      · have := (hrk (Sum.inr j)).2 j
        simpa [(hqh j).2.1] using this
    have : r = (uLo a, vHi a) := Prod.ext (funext hru) (funext hrv)
    rw [← this]; exact hr
  · obtain ⟨r, hr, hrk⟩ := ag1171_join a hne (ι := M ⊕ N) (Sum.elim ph ql) (by
      intro k
      rcases k with i | j
      · exact (hph i).1
      · exact (hql j).1)
    have hru : ∀ i, r.1 i = uHi a i := by
      intro i
      apply le_antisymm
      · exact (hph i).2.2 r hr
      · have := (hrk (Sum.inl i)).1 i
        simpa [(hph i).2.1] using this
    have hrv : ∀ j, r.2 j = vLo a j := by
      intro j
      apply le_antisymm
      · have := (hrk (Sum.inr j)).2 j
        simpa [(hql j).2.1] using this
      · exact (hql j).2.2 r hr
    have : r = (uHi a, vLo a) := Prod.ext (funext hru) (funext hrv)
    rw [← this]; exact hr
  · intro u' u'' v' v'' h' h''
    have h1 : ∀ i, (u' i - u'' i) ^ 2 ≤ (uLo a i - uHi a i) ^ 2 := by
      intro i
      have a1 := (ag1171_uLo a hne i).choose_spec.2.2 _ h'
      have a2 := (ag1171_uLo a hne i).choose_spec.2.2 _ h''
      have b1 := (ag1171_uHi a hne i).choose_spec.2.2 _ h'
      have b2 := (ag1171_uHi a hne i).choose_spec.2.2 _ h''
      have hh : (u' i - u'' i) ^ 2 ≤ (uHi a i - uLo a i) ^ 2 := by
        apply sq_le_sq'
        · simp only at a1 a2 b1 b2; linarith
        · simp only at a1 a2 b1 b2; linarith
      calc (u' i - u'' i) ^ 2 ≤ (uHi a i - uLo a i) ^ 2 := hh
        _ = (uLo a i - uHi a i) ^ 2 := by ring
    have h2 : ∀ j, (v' j - v'' j) ^ 2 ≤ (vHi a j - vLo a j) ^ 2 := by
      intro j
      have a1 := (ag1171_vLo a hne j).choose_spec.2.2 _ h'
      have a2 := (ag1171_vLo a hne j).choose_spec.2.2 _ h''
      have b1 := (ag1171_vHi a hne j).choose_spec.2.2 _ h'
      have b2 := (ag1171_vHi a hne j).choose_spec.2.2 _ h''
      apply sq_le_sq'
      · simp only at a1 a2 b1 b2; linarith
      · simp only at a1 a2 b1 b2; linarith
    exact add_le_add (Finset.sum_le_sum fun i _ => h1 i) (Finset.sum_le_sum fun j _ => h2 j)

/- Source: Scratch_AssignmentGame_matching_extends.lean -/

open AssignmentGame.CoreCorners

theorem matching_extends_to_equiv {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (e : M ≃ N) (P : Finset (M × N))
    (hP : IsMatching Finset.univ Finset.univ P) :
    ∃ f : M ≃ N, ∀ p ∈ P, f p.1 = p.2 := by
  classical
  let f : {p : M × N // p ∈ P} → M := fun p => p.1.1
  let g : {p : M × N // p ∈ P} → M := fun p => e.symm p.1.2
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    exact hP.2.1 p.1 p.2 q.1 q.2 hpq
  have hg : Function.Injective g := by
    intro p q hpq
    apply Subtype.ext
    exact hP.2.2 p.1 p.2 q.1 q.2 (e.symm.injective hpq)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨σ.trans e, ?_⟩
  intro p hp
  have h := hσ ⟨p, hp⟩
  simpa [f, g] using congrArg e h

/- Source: Scratch_AssignmentGame_removed_seller_full_cover.lean -/

open AssignmentGame.CoreCorners

set_option autoImplicit false

theorem removed_seller_full_cover
    {D : Type*} [Fintype D] [DecidableEq D]
    (a : D → D → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (idle j : D) (hidle : ∀ k, a idle k = 0) :
    ∃ f : D ≃ D, f idle = j ∧
      worth a Finset.univ (Finset.univ.erase j) =
        ∑ i ∈ (Finset.univ : Finset D).erase idle, a i (f i) := by
  classical
  obtain ⟨P, hP, hworth⟩ :=
    ag1171_exists_opt a (Finset.univ : Finset D) (Finset.univ.erase j)
  let P' : Finset (D × D) := P.filter (fun p => p.1 ≠ idle)
  have hP' : IsMatching (Finset.univ : Finset D) (Finset.univ : Finset D) P' := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩
    · intro p hp q hq he
      exact hP.2.1 p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 he
    · intro p hp q hq he
      exact hP.2.2 p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 he
  have hweight : (∑ p ∈ P', a p.1 p.2) = ∑ p ∈ P, a p.1 p.2 := by
    simp only [P', Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h : p.1 = idle
    · simp [h, hidle]
    · simp [h]
  let Q : Finset (D × D) := insert (idle,j) P'
  have hQ : IsMatching (Finset.univ : Finset D) (Finset.univ : Finset D) Q := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩
    · intro p hp q hq he
      rcases Finset.mem_insert.1 hp with rfl | hp
      · rcases Finset.mem_insert.1 hq with rfl | hq
        · rfl
        · have hne := (Finset.mem_filter.1 hq).2
          exact False.elim (hne he.symm)
      · rcases Finset.mem_insert.1 hq with rfl | hq
        · have hne := (Finset.mem_filter.1 hp).2
          exact False.elim (hne he)
        · exact hP'.2.1 p hp q hq he
    · intro p hp q hq he
      rcases Finset.mem_insert.1 hp with rfl | hp
      · rcases Finset.mem_insert.1 hq with rfl | hq
        · rfl
        · have hj : q.2 ∈ (Finset.univ : Finset D).erase j :=
            (Finset.mem_product.1 (hP.1 (Finset.mem_filter.1 hq).1)).2
          exact False.elim ((Finset.mem_erase.1 hj).1 he.symm)
      · rcases Finset.mem_insert.1 hq with rfl | hq
        · have hj : p.2 ∈ (Finset.univ : Finset D).erase j :=
            (Finset.mem_product.1 (hP.1 (Finset.mem_filter.1 hp).1)).2
          exact False.elim ((Finset.mem_erase.1 hj).1 he)
        · exact hP'.2.2 p hp q hq he
  obtain ⟨f, hf⟩ := matching_extends_to_equiv (Equiv.refl D) Q hQ
  have hfidle : f idle = j := hf (idle,j) (Finset.mem_insert_self _ _)
  let G : Finset (D × D) :=
    (Finset.univ.erase idle).image (fun i : D => (i, f i))
  have hP'G : P' ⊆ G := by
    intro p hp
    have hpi : p.1 ≠ idle := (Finset.mem_filter.1 hp).2
    apply Finset.mem_image.2
    refine ⟨p.1, Finset.mem_erase.2 ⟨hpi, Finset.mem_univ _⟩, ?_⟩
    exact Prod.ext rfl (hf p (Finset.mem_insert_of_mem hp))
  have hG : IsMatching (Finset.univ : Finset D) (Finset.univ.erase j) G := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      refine Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩⟩
      intro he
      have : i = idle := f.injective (he.trans hfidle.symm)
      exact (Finset.mem_erase.1 hi).1 this
    · intro p hp q hq he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hq
      simpa using congrArg (fun i : D => (i, f i)) he
    · intro p hp q hq he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hq
      exact congrArg (fun i : D => (i, f i)) (f.injective he)
  have hGweight : (∑ p ∈ G, a p.1 p.2) =
      ∑ i ∈ (Finset.univ : Finset D).erase idle, a i (f i) := by
    dsimp only [G]
    rw [Finset.sum_image]
    intro i hi k hk he
    exact congrArg Prod.fst he
  have hle : (∑ p ∈ P', a p.1 p.2) ≤ ∑ p ∈ G, a p.1 p.2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hP'G
    intro p hp hnot
    exact ha p.1 p.2
  refine ⟨f, hfidle, ?_⟩
  have hupper := ag1171_le_worth a hG
  rw [hGweight] at hupper
  rw [hworth, ← hweight]
  have hle' : (∑ p ∈ P', a p.1 p.2) ≤
      ∑ i ∈ (Finset.univ : Finset D).erase idle, a i (f i) := by
    rw [← hGweight]
    exact hle
  have hupper' : (∑ i ∈ (Finset.univ : Finset D).erase idle, a i (f i)) ≤
      ∑ p ∈ P', a p.1 p.2 := by
    rw [hweight, ← hworth]
    exact hupper
  exact le_antisymm hle' hupper'

/- Source: Scratch_AssignmentGame_core_marginal_upper.lean -/

namespace AssignmentGame.CoreCorners

open Finset

variable {M N : Type*} [Fintype M] [Fintype N]
  [DecidableEq N]

/-- A courier's core payoff cannot exceed the loss in assignment worth
when that courier is removed. This is the easy half of the marginal-payoff
identity needed in Lemma 3.2. -/
theorem core_seller_payoff_le_removal_loss
    (a : M → N → ℝ) (u : M → ℝ) (v : N → ℝ)
    (hcore : (u, v) ∈ core a) (j : N) :
    v j ≤ worth a univ univ - worth a univ (univ.erase j) := by
  classical
  have hcoal := hcore.2 (univ : Finset M) (univ.erase j)
  have htotal := hcore.1
  have hsplit : (∑ k : N, v k) = (∑ k ∈ (univ : Finset N).erase j, v k) + v j := by
    simpa using (Finset.sum_erase_add (s := (univ : Finset N))
      (f := v) (Finset.mem_univ j)).symm
  linarith

theorem vHi_le_removal_loss
    (a : M → N → ℝ) (j : N) (hne : (core a).Nonempty) :
    vHi a j ≤ worth a univ univ - worth a univ (univ.erase j) := by
  unfold vHi
  apply csSup_le
  · obtain ⟨⟨u,v⟩,hc⟩ := hne
    exact ⟨v j, ⟨(u,v),hc,rfl⟩⟩
  rintro x ⟨⟨u, v⟩, hcore, rfl⟩
  exact core_seller_payoff_le_removal_loss a u v hcore j

end AssignmentGame.CoreCorners

/- Source: Scratch_AssignmentGame_core_marginal_exact.lean -/

namespace AssignmentGame.CoreCorners

open Finset

variable {M N : Type*} [Fintype M] [Fintype N]
  [DecidableEq M] [DecidableEq N]

/-- In an assignment game with nonnegative edge weights, the largest core
payoff to a seller is exactly that seller's marginal contribution to the
optimal matching. This is the missing assignment-game price identity in
Lemma 3.2 of the pricing-with-tips paper. -/
theorem vHi_eq_removal_loss
    (a : M → N → ℝ) (ha : ∀ i k, 0 ≤ a i k) (j : N) :
    vHi a j = worth a univ univ - worth a univ (univ.erase j) := by
  classical
  let W := worth a (univ : Finset M) (univ : Finset N)
  let W₀ := worth a (univ : Finset M) (univ.erase j)
  let t := W - W₀
  obtain ⟨P₀, hP₀, hP₀val⟩ := ag1171_exists_opt a (univ : Finset M) (univ.erase j)
  have hP₀full : IsMatching (univ : Finset M) (univ : Finset N) P₀ := by
    refine ⟨?_, hP₀.2.1, hP₀.2.2⟩
    intro p hp
    exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  have hP₀no : ∀ p ∈ P₀, p.2 ≠ j := by
    intro p hp he
    have hmem := Finset.mem_product.1 (hP₀.1 hp)
    exact (Finset.mem_erase.1 hmem.2).1 he
  have ht : 0 ≤ t := by
    have hle := ag1171_le_worth a hP₀full
    dsimp [t, W, W₀]
    rw [hP₀val]
    linarith
  let a' : M → N → ℝ := fun i k => if k = j then max 0 (a i k - t) else a i k
  have ha' : ∀ i k, 0 ≤ a' i k := by
    intro i k
    by_cases hk : k = j
    · simp [a', hk]
    · simpa [a', hk] using ha i k
  have hmod₀ : (∑ p ∈ P₀, a' p.1 p.2) = W₀ := by
    change (∑ p ∈ P₀, a' p.1 p.2) = worth a univ (univ.erase j)
    rw [hP₀val]
    apply Finset.sum_congr rfl
    intro p hp
    simp [a', hP₀no p hp]
  have hmod_le : ∀ P : Finset (M × N),
      IsMatching (univ : Finset M) (univ : Finset N) P →
        (∑ p ∈ P, a' p.1 p.2) ≤ W₀ := by
    intro P hP
    by_cases hj : ∃ p ∈ P, p.2 = j
    · obtain ⟨p,hp,hpj⟩ := hj
      let R := P.erase p
      have hR : IsMatching (univ : Finset M) (univ.erase j) R := by
        refine ⟨?_, ?_, ?_⟩
        · intro q hq
          have hqP : q ∈ P := (Finset.mem_erase.1 hq).2
          have hqne : q.2 ≠ j := by
            intro hqj
            have hpq : p = q := hP.2.2 p hp q hqP (hpj.trans hqj.symm)
            exact (Finset.mem_erase.1 hq).1 hpq.symm
          exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_erase.2 ⟨hqne, Finset.mem_univ _⟩⟩
        · intro q hq r hr hqr
          exact hP.2.1 q ((Finset.mem_erase.1 hq).2) r ((Finset.mem_erase.1 hr).2) hqr
        · intro q hq r hr hqr
          exact hP.2.2 q ((Finset.mem_erase.1 hq).2) r ((Finset.mem_erase.1 hr).2) hqr
      have hRval : (∑ q ∈ R, a q.1 q.2) ≤ W₀ := ag1171_le_worth a hR
      have hPval : (∑ q ∈ P, a q.1 q.2) ≤ W := ag1171_le_worth a hP
      have hRmod : (∑ q ∈ R, a' q.1 q.2) = ∑ q ∈ R, a q.1 q.2 := by
        apply Finset.sum_congr rfl
        intro q hq
        have hqj : q.2 ≠ j := by
          have hm := Finset.mem_product.1 (hR.1 hq)
          exact (Finset.mem_erase.1 hm.2).1
        simp [a', hqj]
      have hPsum : (∑ q ∈ P, a q.1 q.2) = (∑ q ∈ R, a q.1 q.2) + a p.1 p.2 := by
        simpa [R] using (Finset.sum_erase_add (s := P)
          (f := fun q : M × N => a q.1 q.2) hp).symm
      have hPmod : (∑ q ∈ P, a' q.1 q.2) =
          (∑ q ∈ R, a q.1 q.2) + max 0 (a p.1 p.2 - t) := by
        have h := (Finset.sum_erase_add (s := P)
          (f := fun q : M × N => a' q.1 q.2) hp).symm
        simpa [R, a', hpj, hRmod] using h
      rw [hPmod]
      by_cases hsign : 0 ≤ a p.1 p.2 - t
      · rw [max_eq_right hsign]
        dsimp [t] at *
        linarith
      · rw [max_eq_left (le_of_not_ge hsign)]
        linarith
    · have hPsmall : IsMatching (univ : Finset M) (univ.erase j) P := by
        refine ⟨?_, hP.2.1, hP.2.2⟩
        intro p hp
        have hpj : p.2 ≠ j := by
          intro he
          exact hj ⟨p,hp,he⟩
        exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_erase.2 ⟨hpj, Finset.mem_univ _⟩⟩
      calc
        (∑ p ∈ P, a' p.1 p.2) = ∑ p ∈ P, a p.1 p.2 := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpj : p.2 ≠ j := by
            intro he
            exact hj ⟨p,hp,he⟩
          simp [a', hpj]
        _ ≤ W₀ := ag1171_le_worth a hPsmall
  have hWmod : worth a' (univ : Finset M) (univ : Finset N) = W₀ := by
    apply le_antisymm
    · exact ag1171_worth_le a' _ _ W₀ hmod_le
    · rw [← hmod₀]
      exact ag1171_le_worth a' hP₀full
  obtain ⟨u,v,hcore'⟩ := ag1171_core_nonempty a' ha'
  have hvzero : v j = 0 :=
    (ag1171_cs a' hcore' hP₀full (hWmod.trans hmod₀.symm)).2.2 j hP₀no
  have hdual' := (ag1171_core_iff a' u v).1 hcore'
  let v' : N → ℝ := fun k => if k = j then t else v k
  have hdual : ag1171_DF a u v' := by
    refine ⟨hdual'.1.1, ?_, ?_⟩
    · intro k
      by_cases hk : k = j
      · simp [v', hk, ht]
      · simpa [v', hk] using hdual'.1.2.1 k
    · intro i k
      by_cases hk : k = j
      · subst k
        have h := hdual'.1.2.2 i j
        simp only [a', ite_true] at h
        simp only [v', ite_true]
        linarith [le_max_right (0 : ℝ) (a i j - t)]
      · have h := hdual'.1.2.2 i k
        simpa [a', v', hk] using h
  have hvsum : (∑ k, v' k) = (∑ k, v k) + t := by
    have h := Finset.sum_erase_add (s := (univ : Finset N)) (f := v) (Finset.mem_univ j)
    have h' := Finset.sum_erase_add (s := (univ : Finset N)) (f := v') (Finset.mem_univ j)
    have he : (∑ k ∈ (univ : Finset N).erase j, v' k) =
        ∑ k ∈ (univ : Finset N).erase j, v k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [v', (Finset.mem_erase.1 hk).1]
    have hvj : v' j = t := by simp [v']
    rw [hvj] at h'
    linarith
  have hcore : (u,v') ∈ core a := by
    apply (ag1171_core_iff a u v').2
    constructor
    · exact hdual
    · have hsum := hdual'.2
      rw [hWmod] at hsum
      rw [hvsum]
      dsimp [W, W₀, t] at *
      linarith
  apply le_antisymm
  · exact vHi_le_removal_loss a j ⟨(u,v'),hcore⟩
  · unfold vHi
    have hbdd : BddAbove (((fun p : (M → ℝ) × (N → ℝ) => p.2 j) '' core a)) := by
      refine ⟨t, ?_⟩
      rintro x ⟨⟨u₀,v₀⟩, hc, rfl⟩
      exact core_seller_payoff_le_removal_loss a u₀ v₀ hc j
    have hmem : v' j ∈ ((fun p : (M → ℝ) × (N → ℝ) => p.2 j) '' core a) :=
      ⟨(u,v'),hcore,rfl⟩
    have hle := le_csSup hbdd hmem
    simpa [v', t, W, W₀] using hle

end AssignmentGame.CoreCorners

/- Source: Sol_PricingWithTips_optimal_has_courier_plan.lean -/

open AssignmentGame.CoreCorners
open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

noncomputable def courierSlot (A : Allocation B S D) (d : D) :
    Option (B × S) := by
  classical
  exact if h : A.CourierWorks d then
    some (Classical.choose h, Classical.choose (Classical.choose_spec h))
  else none

theorem courierSlot_eq_some_of_trade
    (A : Allocation B S D) {b : B} {s : S} {d : D}
    (ht : A.Trades b s d) : courierSlot A d = some (b,s) := by
  classical
  have hwork : A.CourierWorks d := ⟨b,s,ht⟩
  unfold courierSlot
  rw [dif_pos hwork]
  let b₀ := Classical.choose hwork
  let hs := Classical.choose_spec hwork
  let s₀ := Classical.choose hs
  have ht₀ : A.Trades b₀ s₀ d := Classical.choose_spec hs
  have hb : b₀ = b := A.courier_unique ht₀ ht
  have ht₀' : A.Trades b s₀ d := by simpa only [hb] using ht₀
  have hpair : (s₀,d) = (s,d) := Option.some.inj (ht₀'.symm.trans ht)
  have hss : s₀ = s := congrArg Prod.fst hpair
  change some (b₀,s₀) = some (b,s)
  rw [hb,hss]

private theorem courierSlot_trade_of_eq_some
    (A : Allocation B S D) {b : B} {s : S} {d : D}
    (hslot : courierSlot A d = some (b,s)) : A.Trades b s d := by
  classical
  by_cases hwork : A.CourierWorks d
  · obtain ⟨b₀,s₀,ht⟩ := hwork
    rw [courierSlot_eq_some_of_trade A ht] at hslot
    have hp : (b₀,s₀) = (b,s) := Option.some.inj hslot
    cases hp
    exact ht
  · simp [courierSlot, hwork] at hslot

theorem courierSlot_none_iff_idle
    (A : Allocation B S D) (d : D) :
    courierSlot A d = none ↔ ¬ A.CourierWorks d := by
  classical
  constructor
  · intro h hwork
    obtain ⟨b,s,ht⟩ := hwork
    rw [courierSlot_eq_some_of_trade A ht] at h
    contradiction
  · intro h
    simp [courierSlot, h]

theorem sum_assigned_eq_sum_courierSlots
    (A : Allocation B S D) (F : D → B → S → ℝ) :
    (∑ b, match A.assigned b with
      | none => 0
      | some (s,d) => F d b s) =
    ∑ d, match courierSlot A d with
      | none => 0
      | some (b,s) => F d b s := by
  classical
  let T : Finset B := Finset.univ.filter (fun b => (A.assigned b).isSome)
  let U : Finset D := Finset.univ.filter (fun d => A.CourierWorks d)
  let G : B → ℝ := fun b => match A.assigned b with
    | none => 0
    | some (s,d) => F d b s
  let H : D → ℝ := fun d => match courierSlot A d with
    | none => 0
    | some (b,s) => F d b s
  have hfilterB : (∑ b, G b) = ∑ b ∈ T, G b := by
    simp only [T, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    cases h : A.assigned b with
    | none => simp [G, h]
    | some sd => simp [G, h]
  have hfilterD : (∑ d, H d) = ∑ d ∈ U, H d := by
    simp only [U, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : A.CourierWorks d
    · simp [hd]
    · simp [H, (courierSlot_none_iff_idle A d).2 hd, hd]
  have hbij : (∑ d ∈ U, H d) = ∑ b ∈ T, G b := by
    apply Finset.sum_bij (fun d hd => Classical.choose
      (show A.CourierWorks d from (Finset.mem_filter.mp hd).2))
    · intro d hd
      have hwork : A.CourierWorks d := (Finset.mem_filter.mp hd).2
      let b₀ := Classical.choose hwork
      let hs := Classical.choose_spec hwork
      let s₀ := Classical.choose hs
      have ht : A.Trades b₀ s₀ d := Classical.choose_spec hs
      change A.assigned b₀ = some (s₀,d) at ht
      change b₀ ∈ T
      simp [T, ht]
    · intro d₁ hd₁ d₂ hd₂ hb
      have hw₁ : A.CourierWorks d₁ := (Finset.mem_filter.mp hd₁).2
      have hw₂ : A.CourierWorks d₂ := (Finset.mem_filter.mp hd₂).2
      let b₁ := Classical.choose hw₁
      let hs₁ := Classical.choose_spec hw₁
      let s₁ := Classical.choose hs₁
      have ht₁ : A.Trades b₁ s₁ d₁ := Classical.choose_spec hs₁
      let b₂ := Classical.choose hw₂
      let hs₂ := Classical.choose_spec hw₂
      let s₂ := Classical.choose hs₂
      have ht₂ : A.Trades b₂ s₂ d₂ := Classical.choose_spec hs₂
      change b₁ = b₂ at hb
      have ht₁' : A.Trades b₂ s₁ d₁ := by rw [← hb]; exact ht₁
      have hp : some (s₁,d₁) = some (s₂,d₂) := ht₁'.symm.trans ht₂
      exact congrArg Prod.snd (Option.some.inj hp)
    · intro b hb
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      cases h : A.assigned b with
      | none => simp [h] at hb
      | some sd =>
          rcases sd with ⟨s,d⟩
          have ht : A.Trades b s d := h
          have hw : A.CourierWorks d := ⟨b,s,ht⟩
          have hd : d ∈ U := by simp [U,hw]
          refine ⟨d,hd,?_⟩
          let b₀ := Classical.choose hw
          let hs := Classical.choose_spec hw
          let s₀ := Classical.choose hs
          have ht₀ : A.Trades b₀ s₀ d := Classical.choose_spec hs
          exact A.courier_unique ht₀ ht
    · intro d hd
      have hw : A.CourierWorks d := (Finset.mem_filter.mp hd).2
      let b₀ := Classical.choose hw
      let hs := Classical.choose_spec hw
      let s₀ := Classical.choose hs
      have ht : A.Trades b₀ s₀ d := Classical.choose_spec hs
      change A.assigned b₀ = some (s₀,d) at ht
      have hslot : courierSlot A d = some (b₀,s₀) :=
        courierSlot_eq_some_of_trade A ht
      change H d = G b₀
      simp [H,G,hslot,ht]
  simpa only [G,H] using hfilterB.trans (hbij.symm.trans hfilterD.symm)

private theorem cost_le_total
    (M : Market B S D) (d : D) (b : B) (s : S) :
    M.cost d b s ≤ ∑ d' : D, ∑ b' : B, ∑ s' : S, M.cost d' b' s' := by
  have h₁ : M.cost d b s ≤ ∑ s' : S, M.cost d b s' :=
    Finset.single_le_sum (fun s' _ => M.cost_nonneg d b s') (Finset.mem_univ s)
  have h₂ : (∑ s' : S, M.cost d b s') ≤
      ∑ b' : B, ∑ s' : S, M.cost d b' s' :=
    Finset.single_le_sum (fun b' _ => Finset.sum_nonneg (fun s' _ =>
      M.cost_nonneg d b' s')) (Finset.mem_univ b)
  have h₃ : (∑ b' : B, ∑ s' : S, M.cost d b' s') ≤
      ∑ d' : D, ∑ b' : B, ∑ s' : S, M.cost d' b' s' :=
    Finset.single_le_sum (fun d' _ => Finset.sum_nonneg (fun b' _ =>
      Finset.sum_nonneg (fun s' _ => M.cost_nonneg d' b' s')))
      (Finset.mem_univ d)
  exact h₁.trans (h₂.trans h₃)

noncomputable def courierWeight (M : Market B S D) (A : Allocation B S D)
    (C : ℝ) (slot courier : D) : ℝ :=
  match courierSlot A slot with
  | none => 0
  | some (b,s) => C - M.cost courier b s

private theorem courierWeight_nonneg
    (M : Market B S D) (A : Allocation B S D)
    (C : ℝ) (hC : ∀ d b s, M.cost d b s ≤ C)
    (slot courier : D) : 0 ≤ courierWeight M A C slot courier := by
  unfold courierWeight
  cases hslot : courierSlot A slot with
  | none => simp
  | some bs =>
      rcases bs with ⟨b,s⟩
      simp [hC courier b s]

private theorem courierWeight_sum_perm
    (M : Market B S D) (A : Allocation B S D)
    (C : ℝ) (hoptimal : IsWelfareOptimal M A) (f : D ≃ D) :
    (∑ slot, courierWeight M A C slot (f slot)) ≤
      ∑ slot, courierWeight M A C slot slot := by
  classical
  let K : ℝ := ∑ slot, match courierSlot A slot with
    | none => 0
    | some _ => C
  let Q (g : D ≃ D) : ℝ := ∑ slot, match courierSlot A slot with
    | none => 0
    | some (b,s) => M.cost (g slot) b s
  have hdecomp (g : D ≃ D) :
      (∑ slot, courierWeight M A C slot (g slot)) = K - Q g := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro slot _
    cases hslot : courierSlot A slot with
    | none => simp [courierWeight, K, Q, hslot]
    | some bs => cases bs; simp [courierWeight, K, Q, hslot]
  have hcost := optimal_reassign_couriers_cost_le M A hoptimal f
  have hQ : Q (Equiv.refl D) ≤ Q f := by
    change (∑ slot, match courierSlot A slot with
      | none => (0 : ℝ)
      | some (b,s) => M.cost slot b s) ≤
      (∑ slot, match courierSlot A slot with
      | none => (0 : ℝ)
      | some (b,s) => M.cost (f slot) b s)
    calc
      (∑ slot, match courierSlot A slot with
        | none => (0 : ℝ)
        | some (b,s) => M.cost slot b s) =
          (∑ b, match A.assigned b with
            | none => (0 : ℝ)
            | some (s,d) => M.cost d b s) :=
        (sum_assigned_eq_sum_courierSlots A (fun d b s => M.cost d b s)).symm
      _ ≤ (∑ b, match A.assigned b with
            | none => (0 : ℝ)
            | some (s,d) => M.cost (f d) b s) := hcost
      _ = (∑ slot, match courierSlot A slot with
            | none => (0 : ℝ)
            | some (b,s) => M.cost (f slot) b s) :=
        sum_assigned_eq_sum_courierSlots A (fun d b s => M.cost (f d) b s)
  have hdecomp_id : (∑ slot, courierWeight M A C slot slot) =
      K - Q (Equiv.refl D) := by
    simpa using hdecomp (Equiv.refl D)
  rw [hdecomp f, hdecomp_id]
  linarith

theorem optimalCourierSlot_dual
    (M : Market B S D) (A : Allocation B S D)
    (hoptimal : IsWelfareOptimal M A) :
    ∃ (C : ℝ) (u v : D → ℝ),
      (∀ d, 0 ≤ u d) ∧ (∀ d, 0 ≤ v d) ∧
      (∀ slot courier,
        courierWeight M A C slot courier ≤ u slot + v courier) ∧
      (∀ slot, u slot + v slot = courierWeight M A C slot slot) := by
  classical
  let C : ℝ := (∑ d : D, ∑ b : B, ∑ s : S, M.cost d b s) + 1
  have hC : ∀ d b s, M.cost d b s ≤ C := by
    intro d b s
    dsimp [C]
    linarith [cost_le_total M d b s]
  let a : D → D → ℝ := courierWeight M A C
  have ha : ∀ slot courier, 0 ≤ a slot courier := by
    intro slot courier
    exact courierWeight_nonneg M A C hC slot courier
  have hperm : ∀ f : D ≃ D,
      (∑ slot, a slot (f slot)) ≤ ∑ slot, a slot slot := by
    intro f
    exact courierWeight_sum_perm M A C hoptimal f
  have hworth : worth a Finset.univ Finset.univ ≤ ∑ slot, a slot slot :=
    worth_le_permutation_bound a ha (Equiv.refl D) _ hperm
  obtain ⟨⟨u,v⟩, hcore⟩ := core_nonempty a ha
  obtain ⟨hu,hv,hdual⟩ := core_dual_constraints a u v hcore
  have hsumle : (∑ slot, a slot slot) ≤
      (∑ slot, u slot) + (∑ courier, v courier) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun slot _ => hdual slot slot)
  have hworth_eq : (∑ slot, a slot slot) =
      (∑ slot, u slot) + (∑ courier, v courier) := by
    have hcoreeq : (∑ slot, u slot) + (∑ courier, v courier) =
        worth a Finset.univ Finset.univ := hcore.1
    linarith
  have htight : ∀ slot, u slot + v slot = a slot slot := by
    intro slot
    have hgap_nonneg : ∀ slot, 0 ≤ u slot + v slot - a slot slot := by
      intro i
      linarith [hdual i i]
    have hgap_sum : (∑ i : D, (u i + v i - a i i)) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      linarith
    have hgap_le := Finset.single_le_sum (f := fun i : D => u i + v i - a i i)
      (fun i _ => hgap_nonneg i) (Finset.mem_univ slot)
    rw [hgap_sum] at hgap_le
    linarith [hgap_nonneg slot]
  exact ⟨C,u,v,hu,hv,hdual,htight⟩

private noncomputable def dualWage (A : Allocation B S D)
    (C : ℝ) (u : D → ℝ) (b : B) (s : S) : ℝ := by
  classical
  exact if h : A.Delivers b s then C - u (Classical.choose h) else 0

private theorem dualWage_eq_of_trade
    (A : Allocation B S D) (C : ℝ) (u : D → ℝ)
    {b : B} {s : S} {d : D} (ht : A.Trades b s d) :
    dualWage A C u b s = C - u d := by
  classical
  have hd : A.Delivers b s := ⟨d,ht⟩
  unfold dualWage
  rw [dif_pos hd]
  have hc : A.Trades b s (Classical.choose hd) := Classical.choose_spec hd
  have hp : some (s,Classical.choose hd) = some (s,d) := hc.symm.trans ht
  have he : Classical.choose hd = d := congrArg Prod.snd (Option.some.inj hp)
  rw [he]

private theorem dualWage_zero_off
    (A : Allocation B S D) (C : ℝ) (u : D → ℝ)
    (b : B) (s : S) (hd : ¬ A.Delivers b s) :
    dualWage A C u b s = 0 := by
  classical
  simp [dualWage, hd]

/- Source: Scratch_PricingWithTips_courier_corner_plan.lean -/

open AssignmentGame.CoreCorners
open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

private theorem realized_eq_trade_corner
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
  have hp : (s₀,d) = (s,d) := Option.some.inj (ht₀'.symm.trans ht)
  have hss : s₀ = s := congrArg Prod.fst hp
  change w b₀ s₀ - M.cost d b₀ s₀ = w b s - M.cost d b s
  rw [hb,hss]

private theorem cost_le_total_corner
    (M : Market B S D) (d : D) (b : B) (s : S) :
    M.cost d b s ≤ ∑ d' : D, ∑ b' : B, ∑ s' : S, M.cost d' b' s' := by
  have h₁ : M.cost d b s ≤ ∑ s' : S, M.cost d b s' :=
    Finset.single_le_sum (fun s' _ => M.cost_nonneg d b s') (Finset.mem_univ s)
  have h₂ : (∑ s' : S, M.cost d b s') ≤
      ∑ b' : B, ∑ s' : S, M.cost d b' s' :=
    Finset.single_le_sum (fun b' _ => Finset.sum_nonneg (fun s' _ =>
      M.cost_nonneg d b' s')) (Finset.mem_univ b)
  have h₃ : (∑ b' : B, ∑ s' : S, M.cost d b' s') ≤
      ∑ d' : D, ∑ b' : B, ∑ s' : S, M.cost d' b' s' :=
    Finset.single_le_sum (fun d' _ => Finset.sum_nonneg (fun b' _ =>
      Finset.sum_nonneg (fun s' _ => M.cost_nonneg d' b' s')))
      (Finset.mem_univ d)
  exact h₁.trans (h₂.trans h₃)

/-- The high-seller-payoff core corner of the courier assignment game
produces an actual courier plan. -/
theorem exists_courier_corner_plan
    (M : Market B S D) (A : Allocation B S D)
    (hoptimal : IsWelfareOptimal M A) :
    ∃ C : ℝ, ∃ w : B → S → ℝ,
      (∀ d b s, M.cost d b s < C) ∧ IsCourierPlanFor M A w ∧
      (worth (fun slot courier => max 0 (courierWeight M A C slot courier))
        Finset.univ Finset.univ =
        ∑ slot : D, match courierSlot A slot with
          | none => (0 : ℝ)
          | some (b,s) => C - M.cost slot b s) ∧
      ∀ d, courierRealizedUtility M A w d =
        vHi (fun slot courier => max 0 (courierWeight M A C slot courier)) d := by
  classical
  obtain ⟨Cbase,ubase,v₀,hubase,hv₀,hdualbase,htightbase⟩ :=
    optimalCourierSlot_dual M A hoptimal
  let C : ℝ := max Cbase ((∑ d : D, ∑ b : B, ∑ s : S, M.cost d b s) + 1)
  let Δ : ℝ := C - Cbase
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ, C]
    linarith [le_max_left Cbase ((∑ d : D, ∑ b : B, ∑ s : S, M.cost d b s) + 1)]
  have hC : ∀ d b s, M.cost d b s < C := by
    intro d b s
    dsimp [C]
    linarith [cost_le_total_corner M d b s,
      le_max_right Cbase ((∑ d' : D, ∑ b' : B, ∑ s' : S, M.cost d' b' s') + 1)]
  let u₀ : D → ℝ := fun slot => ubase slot +
    if (courierSlot A slot).isSome then Δ else 0
  have hu₀ : ∀ d, 0 ≤ u₀ d := by
    intro d
    dsimp [u₀]
    split_ifs <;> linarith [hubase d, hΔ]
  have hdual₀ : ∀ slot courier,
      courierWeight M A C slot courier ≤ u₀ slot + v₀ courier := by
    intro slot courier
    have hbase := hdualbase slot courier
    cases hslot : courierSlot A slot with
    | none =>
        simp [courierWeight, hslot, u₀] at *
        linarith
    | some bs =>
        rcases bs with ⟨b,s⟩
        simp [courierWeight, hslot, u₀, Δ] at *
        linarith
  have htight₀ : ∀ slot,
      u₀ slot + v₀ slot = courierWeight M A C slot slot := by
    intro slot
    have hbase := htightbase slot
    cases hslot : courierSlot A slot with
    | none =>
        simp [courierWeight, hslot, u₀] at *
        linarith
    | some bs =>
        rcases bs with ⟨b,s⟩
        simp [courierWeight, hslot, u₀, Δ] at *
        linarith
  let a : D → D → ℝ := fun slot courier =>
    max 0 (courierWeight M A C slot courier)
  have ha : ∀ slot courier, 0 ≤ a slot courier := by
    intro slot courier
    exact le_max_left _ _
  have hdiag : ∀ d, a d d = courierWeight M A C d d := by
    intro d
    apply max_eq_right
    linarith [hu₀ d, hv₀ d, htight₀ d]
  have hdf₀ : ag1171_DF a u₀ v₀ := by
    refine ⟨hu₀, hv₀, ?_⟩
    intro slot courier
    exact max_le (by linarith [hu₀ slot, hv₀ courier]) (hdual₀ slot courier)
  let Pdiag : Finset (D × D) := Finset.univ.image (fun d : D => (d,d))
  have hPdiag : IsMatching (Finset.univ : Finset D) (Finset.univ : Finset D) Pdiag := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩
    · intro p hp q hq he
      obtain ⟨d,_,rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨e,_,rfl⟩ := Finset.mem_image.1 hq
      simpa using congrArg (fun d : D => (d,d)) he
    · intro p hp q hq he
      obtain ⟨d,_,rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨e,_,rfl⟩ := Finset.mem_image.1 hq
      simpa using congrArg (fun d : D => (d,d)) he
  have hPsum : (∑ p ∈ Pdiag, a p.1 p.2) = ∑ d, a d d := by
    simp only [Pdiag]
    rw [Finset.sum_image]
    intro d _ e _ he
    exact congrArg Prod.fst he
  have hdiag_dual : (∑ d, a d d) = (∑ d, u₀ d) + ∑ d, v₀ d := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [hdiag]
    exact (htight₀ d).symm
  have hWle : worth a Finset.univ Finset.univ ≤ ∑ d, a d d := by
    rw [hdiag_dual]
    apply ag1171_worth_le
    intro P hP
    exact ag1171_matching_sum_le a u₀ v₀ hdf₀ hP
  have hWge : (∑ d, a d d) ≤ worth a Finset.univ Finset.univ := by
    rw [← hPsum]
    exact ag1171_le_worth a hPdiag
  have hWdiag : worth a Finset.univ Finset.univ = ∑ d, a d d :=
    le_antisymm hWle hWge
  let u : D → ℝ := uLo a
  let v : D → ℝ := vHi a
  have hcore : (u,v) ∈ core a := (core_corners_accepted a ha).1
  have hdf := (ag1171_core_iff a u v).1 hcore
  have hcs := ag1171_cs a hcore hPdiag (hWdiag.trans hPsum.symm)
  have htight : ∀ d, u d + v d = a d d := by
    intro d
    apply hcs.1 (d,d)
    simp [Pdiag]
  let w : B → S → ℝ := fun b s =>
    if h : A.Delivers b s then C - u (Classical.choose h) else 0
  have hwtrade : ∀ {b s d}, A.Trades b s d → w b s = C - u d := by
    intro b s d ht
    have hd : A.Delivers b s := ⟨d,ht⟩
    simp only [w, dif_pos hd]
    have hc : A.Trades b s (Classical.choose hd) := Classical.choose_spec hd
    have hp : some (s,Classical.choose hd) = some (s,d) := hc.symm.trans ht
    have he : Classical.choose hd = d := congrArg Prod.snd (Option.some.inj hp)
    rw [he]
  have hwoff : ∀ b s, ¬ A.Delivers b s → w b s = 0 := by
    intro b s hd
    simp [w, hd]
  have hnet : ∀ d b s, w b s - M.cost d b s ≤ v d := by
    intro d b s
    by_cases hd : A.Delivers b s
    · let d₀ := Classical.choose hd
      have ht₀ : A.Trades b s d₀ := Classical.choose_spec hd
      have hslot : courierSlot A d₀ = some (b,s) :=
        courierSlot_eq_some_of_trade A ht₀
      have hdual := hdf.1.2.2 d₀ d
      have hcw : courierWeight M A C d₀ d ≤ a d₀ d := le_max_right _ _
      simp only [courierWeight, hslot] at hdual hcw
      rw [hwtrade ht₀]
      linarith
    · rw [hwoff b s hd]
      linarith [M.cost_nonneg d b s, hdf.1.2.1 d]
  have hplan : IsCourierPlanFor M A w := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b s
      by_cases hd : A.Delivers b s
      · obtain ⟨d,htrade⟩ := hd
        have hslot : courierSlot A d = some (b,s) :=
          courierSlot_eq_some_of_trade A htrade
        have htd := htight d
        rw [hdiag] at htd
        simp only [courierWeight, hslot] at htd
        rw [hwtrade htrade]
        linarith [M.cost_nonneg d b s, hdf.1.2.1 d]
      · rw [hwoff b s hd]
    · intro d b s htrade
      have hslot : courierSlot A d = some (b,s) :=
        courierSlot_eq_some_of_trade A htrade
      have ht := htight d
      rw [hdiag] at ht
      simp only [courierWeight, hslot] at ht
      have hw := hwtrade htrade
      constructor
      · rw [hw]
        linarith [hdf.1.2.1 d]
      · intro b' s'
        have hle := hnet d b' s'
        rw [hw]
        linarith
    · intro d hd b s
      have hslot : courierSlot A d = none :=
        (courierSlot_none_iff_idle A d).2 hd
      have ht := htight d
      rw [hdiag] at ht
      simp only [courierWeight, hslot] at ht
      have hvzero : v d = 0 := by
        linarith [hdf.1.1 d, hdf.1.2.1 d]
      linarith [hnet d b s]
    · intro b s hd
      exact hwoff b s hd
  have hfullcost : worth a Finset.univ Finset.univ =
      ∑ slot : D, match courierSlot A slot with
        | none => (0 : ℝ)
        | some (b,s) => C - M.cost slot b s := by
    rw [hWdiag]
    apply Finset.sum_congr rfl
    intro slot _
    rw [hdiag]
    cases hslot : courierSlot A slot with
    | none => simp [courierWeight, hslot]
    | some bs => rcases bs with ⟨b,s⟩; simp [courierWeight, hslot]
  refine ⟨C,w,hC,hplan,hfullcost,?_⟩
  intro d
  by_cases hd : A.CourierWorks d
  · obtain ⟨b,s,htrade⟩ := hd
    have hslot : courierSlot A d = some (b,s) :=
      courierSlot_eq_some_of_trade A htrade
    have ht := htight d
    rw [hdiag] at ht
    simp only [courierWeight, hslot] at ht
    rw [realized_eq_trade_corner M A w htrade, hwtrade htrade]
    linarith
  · have hslot : courierSlot A d = none :=
      (courierSlot_none_iff_idle A d).2 hd
    have ht := htight d
    rw [hdiag] at ht
    simp only [courierWeight, hslot] at ht
    have hvzero : v d = 0 := by linarith [hdf.1.1 d, hdf.1.2.1 d]
    unfold courierRealizedUtility
    have hz : ¬ ∃ b s, A.Trades b s d := hd
    rw [dif_neg hz]
    change (0 : ℝ) = v d
    exact hvzero.symm

theorem maximalCourierUtility_ge_courier_worth_loss
    (M : Market B S D) (A : Allocation B S D)
    (hoptimal : IsWelfareOptimal M A)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar) :
    ∃ C : ℝ, (∀ d b s, M.cost d b s < C) ∧
      (worth (fun slot courier =>
          max 0 (courierWeight M A C slot courier)) Finset.univ Finset.univ =
        ∑ slot : D, match courierSlot A slot with
          | none => (0 : ℝ)
          | some (b,s) => C - M.cost slot b s) ∧
      ∀ d, worth (fun slot courier =>
          max 0 (courierWeight M A C slot courier)) Finset.univ Finset.univ -
        worth (fun slot courier =>
          max 0 (courierWeight M A C slot courier))
          Finset.univ (Finset.univ.erase d) ≤ uBar d := by
  obtain ⟨C,w,hC,hplan,hfull,hreal⟩ := exists_courier_corner_plan M A hoptimal
  refine ⟨C,hC,hfull,?_⟩
  intro d
  let a : D → D → ℝ := fun slot courier =>
    max 0 (courierWeight M A C slot courier)
  have ha : ∀ slot courier, 0 ≤ a slot courier := by
    intro slot courier
    exact le_max_left _ _
  have hmax := hu.2 w hplan d
  rw [hreal d, vHi_eq_removal_loss a ha d] at hmax
  exact hmax

/- Source: Scratch_PricingWithTips_courier_loss_cost_gap.lean -/

open AssignmentGame.CoreCorners
open PricingWithTips

set_option autoImplicit false

theorem courier_worth_loss_gives_cost_reassignment
    {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
    [DecidableEq B] [DecidableEq S] [DecidableEq D]
    (M : Market B S D) (A : Allocation B S D) (C : ℝ)
    (hC : ∀ d b s, M.cost d b s < C)
    (idle j : D) (hidle : ¬ A.CourierWorks idle)
    (u : ℝ)
    (hfull : worth (fun slot courier =>
      max 0 (courierWeight M A C slot courier)) Finset.univ Finset.univ =
      ∑ slot : D, match courierSlot A slot with
        | none => (0 : ℝ)
        | some (b,s) => C - M.cost slot b s)
    (hu : worth (fun slot courier =>
      max 0 (courierWeight M A C slot courier)) Finset.univ Finset.univ -
      worth (fun slot courier =>
      max 0 (courierWeight M A C slot courier)) Finset.univ
        (Finset.univ.erase j) ≤ u) :
    ∃ f : D ≃ D, f idle = j ∧
      (∑ slot : D, match courierSlot A slot with
        | none => (0 : ℝ)
        | some (b,s) => M.cost (f slot) b s) -
      (∑ slot : D, match courierSlot A slot with
        | none => (0 : ℝ)
        | some (b,s) => M.cost slot b s) ≤ u := by
  classical
  let a : D → D → ℝ := fun slot courier =>
    max 0 (courierWeight M A C slot courier)
  have ha : ∀ slot courier, 0 ≤ a slot courier := by
    intro slot courier
    exact le_max_left _ _
  have hrow : ∀ courier, a idle courier = 0 := by
    intro courier
    simp [a, courierWeight, (courierSlot_none_iff_idle A idle).2 hidle]
  obtain ⟨f,hfj,hwithout⟩ := removed_seller_full_cover a ha idle j hrow
  have hweight (g : D → D) : (∑ slot : D, a slot (g slot)) =
      ∑ slot : D, match courierSlot A slot with
        | none => (0 : ℝ)
        | some (b,s) => C - M.cost (g slot) b s := by
    apply Finset.sum_congr rfl
    intro slot _
    cases hs : courierSlot A slot with
    | none => simp [a, courierWeight, hs]
    | some bs =>
      rcases bs with ⟨b,s⟩
      have hc := hC (g slot) b s
      simp [a, courierWeight, hs, max_eq_right (le_of_lt (sub_pos.2 hc))]
  have herase : (∑ slot ∈ (Finset.univ : Finset D).erase idle, a slot (f slot)) =
      ∑ slot : D, a slot (f slot) := by
    calc
      _ = (∑ slot ∈ (Finset.univ : Finset D).erase idle, a slot (f slot)) +
          a idle (f idle) := by simp [hrow]
      _ = ∑ slot : D, a slot (f slot) :=
        Finset.sum_erase_add _ _ (Finset.mem_univ idle)
  have hwithout' : worth a Finset.univ (Finset.univ.erase j) =
      ∑ slot : D, a slot (f slot) := by
    exact hwithout.trans herase
  have hfull' : worth a Finset.univ Finset.univ =
      ∑ slot : D, a slot slot := by
    rw [hweight (fun slot => slot)]
    exact hfull
  have hsumf := hweight f
  have hsumid := hweight (fun slot => slot)
  refine ⟨f,hfj,?_⟩
  change (∑ slot : D, match courierSlot A slot with
        | none => (0 : ℝ)
        | some (b,s) => M.cost (f slot) b s) -
      (∑ slot : D, match courierSlot A slot with
        | none => (0 : ℝ)
        | some (b,s) => M.cost slot b s) ≤ u
  have hK (g : D → D) :
      (∑ slot : D, match courierSlot A slot with
        | none => (0 : ℝ)
        | some (b,s) => C - M.cost (g slot) b s) =
      (∑ slot : D, match courierSlot A slot with
        | none => (0 : ℝ)
        | some _ => C) -
      (∑ slot : D, match courierSlot A slot with
        | none => (0 : ℝ)
        | some (b,s) => M.cost (g slot) b s) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro slot _
    cases hs : courierSlot A slot with
    | none => simp [hs]
    | some bs => rcases bs with ⟨b,s⟩; simp [hs]
  rw [hfull', hwithout', hsumid, hsumf] at hu
  rw [hK, hK] at hu
  linarith

namespace PricingWithTips

theorem maximalCourierUtility_ge_reassignment_cost_gap
    {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
    [DecidableEq B] [DecidableEq S] [DecidableEq D]
    (M : Market B S D) (A : Allocation B S D)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar) :
    ∃ idle : D, ¬ A.CourierWorks idle ∧
      ∀ j : D, ∃ f : D ≃ D, f idle = j ∧
        (∑ slot : D, match courierSlot A slot with
          | none => (0 : ℝ)
          | some (b,s) => M.cost (f slot) b s) -
        (∑ slot : D, match courierSlot A slot with
          | none => (0 : ℝ)
          | some (b,s) => M.cost slot b s) ≤ uBar j := by
  classical
  obtain ⟨idle, hidle⟩ := not_forall.mp hnotfull
  obtain ⟨C,hC,hfull,hgap⟩ :=
    maximalCourierUtility_ge_courier_worth_loss M A hoptimal uBar hu
  refine ⟨idle,hidle,?_⟩
  intro j
  exact courier_worth_loss_gives_cost_reassignment M A C hC idle j hidle
    (uBar j) hfull (hgap j)

end PricingWithTips

/- Source: Scratch_PricingWithTips_unsold_store_pointwise.lean -/

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

private def addNewStoreWithReassignedCouriers
    (A : Allocation B S D) (idle d : D) (hidle : ¬ A.CourierWorks idle)
    (f : D ≃ D) (hfidle : f idle = d)
    (b : B) (s : S) (hunsold : ¬ A.Sells s) : Allocation B S D where
  assigned := fun b' => if b' = b then some (s,d) else
    (A.assigned b').map (fun sd => (sd.1, f sd.2))
  store_unique := by
    intro b₁ b₂ t d₁ d₂ h₁ h₂
    by_cases hb₁ : b₁ = b <;> by_cases hb₂ : b₂ = b
    · exact hb₁.trans hb₂.symm
    · simp only [hb₁, ↓reduceIte] at h₁
      have ht : t = s := congrArg Prod.fst (Option.some.inj h₁).symm
      simp only [hb₂, ↓reduceIte, Option.map_eq_some_iff] at h₂
      obtain ⟨⟨t₂,e₂⟩, ha₂, he₂⟩ := h₂
      have ht₂ : t₂ = t := congrArg Prod.fst he₂
      have hsold : A.Sells s := ⟨b₂,e₂,by simpa [Allocation.Trades, ht₂, ht] using ha₂⟩
      exact False.elim (hunsold hsold)
    · simp only [hb₂, ↓reduceIte] at h₂
      have ht : t = s := congrArg Prod.fst (Option.some.inj h₂).symm
      simp only [hb₁, ↓reduceIte, Option.map_eq_some_iff] at h₁
      obtain ⟨⟨t₁,e₁⟩, ha₁, he₁⟩ := h₁
      have ht₁ : t₁ = t := congrArg Prod.fst he₁
      have hsold : A.Sells s := ⟨b₁,e₁,by simpa [Allocation.Trades, ht₁, ht] using ha₁⟩
      exact False.elim (hunsold hsold)
    · simp only [hb₁, hb₂, ↓reduceIte, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨⟨t₁,e₁⟩, ha₁, he₁⟩ := h₁
      obtain ⟨⟨t₂,e₂⟩, ha₂, he₂⟩ := h₂
      have ht₁ : t₁ = t := congrArg Prod.fst he₁
      have ht₂ : t₂ = t := congrArg Prod.fst he₂
      exact A.store_unique (by simpa [ht₁] using ha₁)
        (by simpa [ht₂] using ha₂)
  courier_unique := by
    intro b₁ b₂ s₁ s₂ e h₁ h₂
    by_cases hb₁ : b₁ = b <;> by_cases hb₂ : b₂ = b
    · exact hb₁.trans hb₂.symm
    · simp only [hb₁, ↓reduceIte] at h₁
      have he : e = d := congrArg Prod.snd (Option.some.inj h₁).symm
      simp only [hb₂, ↓reduceIte, Option.map_eq_some_iff] at h₂
      obtain ⟨⟨t₂,e₂⟩, ha₂, hp₂⟩ := h₂
      have hfe₂ : f e₂ = e := congrArg Prod.snd hp₂
      have he₂ : e₂ = idle := f.injective ((hfe₂.trans he).trans hfidle.symm)
      exact False.elim (hidle ⟨b₂,t₂,by simpa [Allocation.Trades, he₂] using ha₂⟩)
    · simp only [hb₂, ↓reduceIte] at h₂
      have he : e = d := congrArg Prod.snd (Option.some.inj h₂).symm
      simp only [hb₁, ↓reduceIte, Option.map_eq_some_iff] at h₁
      obtain ⟨⟨t₁,e₁⟩, ha₁, hp₁⟩ := h₁
      have hfe₁ : f e₁ = e := congrArg Prod.snd hp₁
      have he₁ : e₁ = idle := f.injective ((hfe₁.trans he).trans hfidle.symm)
      exact False.elim (hidle ⟨b₁,t₁,by simpa [Allocation.Trades, he₁] using ha₁⟩)
    · simp only [hb₁, hb₂, ↓reduceIte, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨⟨t₁,e₁⟩, ha₁, hp₁⟩ := h₁
      obtain ⟨⟨t₂,e₂⟩, ha₂, hp₂⟩ := h₂
      have hfe₁ : f e₁ = e := congrArg Prod.snd hp₁
      have hfe₂ : f e₂ = e := congrArg Prod.snd hp₂
      have he : e₁ = e₂ := f.injective (hfe₁.trans hfe₂.symm)
      subst e₂
      exact A.courier_unique ha₁ ha₂

private theorem sum_replace_one (g h : B → ℝ) (b : B)
    (hag : ∀ x, x ≠ b → h x = g x) :
    (∑ x : B, h x) = (∑ x : B, g x) - g b + h b := by
  classical
  have h₁ : (∑ x : B, h x) =
      (∑ x ∈ (Finset.univ : Finset B).erase b, h x) + h b := by
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ b)).symm
  have h₂ : (∑ x : B, g x) =
      (∑ x ∈ (Finset.univ : Finset B).erase b, g x) + g b := by
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ b)).symm
  rw [h₁, h₂]
  have hs : (∑ x ∈ (Finset.univ : Finset B).erase b, h x) =
      ∑ x ∈ (Finset.univ : Finset B).erase b, g x := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hag x (Finset.mem_erase.1 hx).1
  rw [hs]
  ring

theorem unsold_store_value_le_original_plus_cost_utility
    (M : Market B S D) (A : Allocation B S D)
    (hoptimal : IsWelfareOptimal M A)
    (idle d : D) (hidle : ¬ A.CourierWorks idle)
    (f : D ≃ D) (hfidle : f idle = d)
    (u : ℝ)
    (hgap :
      (∑ slot : D, match courierSlot A slot with
        | none => (0 : ℝ)
        | some (b,s) => M.cost (f slot) b s) -
      (∑ slot : D, match courierSlot A slot with
        | none => (0 : ℝ)
        | some (b,s) => M.cost slot b s) ≤ u)
    (b : B) (s : S) (hunsold : ¬ A.Sells s) :
    M.value b s - M.cost d b s - u ≤
      match A.assigned b with
        | none => (0 : ℝ)
        | some (s₀,_) => M.value b s₀ := by
  classical
  let A' := addNewStoreWithReassignedCouriers A idle d hidle f hfidle b s hunsold
  let V : ℝ := ∑ x : B, match A.assigned x with
    | none => (0 : ℝ)
    | some (t,_) => M.value x t
  let Cid : ℝ := ∑ x : B, match A.assigned x with
    | none => (0 : ℝ)
    | some (t,e) => M.cost e x t
  let Cf : ℝ := ∑ x : B, match A.assigned x with
    | none => (0 : ℝ)
    | some (t,e) => M.cost (f e) x t
  let vb : ℝ := match A.assigned b with
    | none => 0
    | some (t,_) => M.value b t
  let cb : ℝ := match A.assigned b with
    | none => 0
    | some (t,e) => M.cost (f e) b t
  have hcb : 0 ≤ cb := by
    dsimp [cb]
    split <;> simp [M.cost_nonneg]
  have hgap' : Cf - Cid ≤ u := by
    have hCf : Cf = ∑ slot : D, match courierSlot A slot with
        | none => (0 : ℝ)
        | some (x,t) => M.cost (f slot) x t := by
      convert (sum_assigned_eq_sum_courierSlots A
        (fun e x t => M.cost (f e) x t)) using 1 <;> rfl
    have hCid : Cid = ∑ slot : D, match courierSlot A slot with
        | none => (0 : ℝ)
        | some (x,t) => M.cost slot x t := by
      convert (sum_assigned_eq_sum_courierSlots A
        (fun e x t => M.cost e x t)) using 1 <;> rfl
    rw [hCf, hCid]
    exact hgap
  have hW : welfare M A = V - Cid := by
    unfold welfare
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    cases hx : A.assigned x with
    | none => simp [V, Cid, hx]
    | some td => rcases td with ⟨t,e⟩; simp [V, Cid, hx]
  have hW' : welfare M A' = V - Cf - vb + cb +
      (M.value b s - M.cost d b s) := by
    let g : B → ℝ := fun x => match A.assigned x with
      | none => 0
      | some (t,e) => M.value x t - M.cost (f e) x t
    let h : B → ℝ := fun x => match A'.assigned x with
      | none => 0
      | some (t,e) => M.value x t - M.cost e x t
    have haway : ∀ x, x ≠ b → h x = g x := by
      intro x hx
      simp only [h, g, A', addNewStoreWithReassignedCouriers, hx, ↓reduceIte]
      cases ha : A.assigned x with
      | none => simp [ha]
      | some te => rcases te with ⟨t,e⟩; simp [ha]
    have hsum := sum_replace_one g h b haway
    have hgb : g b = vb - cb := by
      dsimp [g, vb, cb]
      cases ha : A.assigned b with
      | none => simp [ha]
      | some te => rcases te with ⟨t,e⟩; simp [ha]
    have hhb : h b = M.value b s - M.cost d b s := by
      simp [h, A', addNewStoreWithReassignedCouriers]
    have hsumg : (∑ x : B, g x) = V - Cf := by
      dsimp [g, V, Cf]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      cases ha : A.assigned x with
      | none => simp [ha]
      | some te => rcases te with ⟨t,e⟩; simp [ha]
    change (∑ x : B, h x) = _
    rw [hsum, hsumg, hgb, hhb]
    ring
  have hopt := hoptimal A'
  rw [hW, hW'] at hopt
  change M.value b s - M.cost d b s - u ≤ vb
  linarith

theorem unsold_store_adjustedValue_le_original_value
    (M : Market B S D) (A : Allocation B S D)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar)
    (b : B) (s : S) (hunsold : ¬ A.Sells s) :
    adjustedValue M A uBar b s ≤
      match A.assigned b with
        | none => (0 : ℝ)
        | some (s₀,_) => M.value b s₀ := by
  classical
  obtain ⟨idle,hidle,hall⟩ :=
    maximalCourierUtility_ge_reassignment_cost_gap M A hoptimal hnotfull uBar hu
  letI : Nonempty D := ⟨idle⟩
  have hcost : ∀ d : D,
      M.value b s - M.cost d b s - uBar d ≤
        (match A.assigned b with
          | none => (0 : ℝ)
          | some (s₀,_) => M.value b s₀) := by
    intro d
    obtain ⟨f,hfidle,hgap⟩ := hall d
    exact unsold_store_value_le_original_plus_cost_utility M A hoptimal
      idle d hidle f hfidle (uBar d) hgap b s hunsold
  have hoff : ¬ A.Delivers b s := by
    rintro ⟨d,ht⟩
    exact hunsold ⟨b,d,ht⟩
  have hinf : M.value b s -
      (match A.assigned b with
        | none => (0 : ℝ)
        | some (s₀,_) => M.value b s₀) ≤
      ⨅ d : D, M.cost d b s + uBar d := by
    apply le_ciInf
    intro d
    linarith [hcost d]
  unfold adjustedValue requiredTip
  rw [if_neg hoff]
  linarith

end PricingWithTips

/- Source: Scratch_PricingWithTips_buyer_matching_prices.lean -/

open PricingWithTips

variable {B S : Type*} [Fintype B] [Fintype S]
  [DecidableEq B] [DecidableEq S]

theorem buyerMatching_sum_prices (z : BuyerMatching B S) (p : S → ℝ) :
    (∑ b, match z.assigned b with | none => 0 | some s => p s) =
      ∑ s, if ∃ b, z.assigned b = some s then p s else 0 := by
  classical
  have hpoint (b : B) :
      (match z.assigned b with | none => 0 | some s => p s) =
        ∑ s, if z.assigned b = some s then p s else 0 := by
    cases h : z.assigned b with
    | none => simp [h]
    | some s => simp [h]
  calc
    (∑ b, match z.assigned b with | none => 0 | some s => p s) =
        ∑ b, ∑ s, if z.assigned b = some s then p s else 0 := by
          apply Finset.sum_congr rfl
          intro b _
          exact hpoint b
    _ = ∑ s, ∑ b, if z.assigned b = some s then p s else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ s, if ∃ b, z.assigned b = some s then p s else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases h : ∃ b, z.assigned b = some s
          · obtain ⟨b₀, hb₀⟩ := h
            have hequiv (b : B) : (z.assigned b = some s) ↔ b = b₀ := by
              constructor
              · intro hb
                exact z.store_unique hb hb₀
              · intro hb
                subst b
                exact hb₀
            have hh : ∃ b, z.assigned b = some s := ⟨b₀, hb₀⟩
            simp only [if_pos hh]
            simp_rw [hequiv]
            simp
          · have hnone (b : B) : z.assigned b ≠ some s := by
              intro hb
              exact h ⟨b, hb⟩
            simp [h, hnone]

theorem buyerMatching_maximum_of_prices
    (z : BuyerMatching B S) (q : B → S → ℝ) (p : S → ℝ)
    (hp : ∀ s, 0 ≤ p s)
    (hbuyer : ∀ b,
      match z.assigned b with
      | none => ∀ s, q b s - p s ≤ 0
      | some s =>
          0 ≤ q b s - p s ∧ ∀ s', q b s' - p s' ≤ q b s - p s)
    (hunsold : ∀ s, (¬ ∃ b, z.assigned b = some s) → p s = 0) :
    IsMaximumWeight z q := by
  classical
  let u : B → ℝ := fun b =>
    match z.assigned b with
    | none => 0
    | some s => q b s - p s
  have hu : ∀ b, 0 ≤ u b := by
    intro b
    cases h : z.assigned b with
    | none => simp [u, h]
    | some s =>
        have hb := hbuyer b
        simp only [h] at hb
        simpa [u, h] using hb.1
  have hdual : ∀ b s, q b s ≤ u b + p s := by
    intro b s
    cases h : z.assigned b with
    | none =>
        have hb := hbuyer b
        simp only [h] at hb
        simp only [u, h]
        linarith [hb s]
    | some s₀ =>
        have hb := hbuyer b
        simp only [h] at hb
        have hb' := hb.2 s
        simp only [u, h]
        linarith
  have hprice (z' : BuyerMatching B S) :
      (∑ b, match z'.assigned b with | none => 0 | some s => p s) ≤ ∑ s, p s := by
    rw [buyerMatching_sum_prices]
    apply Finset.sum_le_sum
    intro s _
    split_ifs with hs
    · exact le_refl _
    · exact hp s
  have hupper (z' : BuyerMatching B S) :
      matchingWeight z' q ≤ (∑ b, u b) + (∑ s, p s) := by
    calc
      matchingWeight z' q ≤
          ∑ b, (u b + match z'.assigned b with | none => 0 | some s => p s) := by
            unfold matchingWeight
            apply Finset.sum_le_sum
            intro b _
            cases h : z'.assigned b with
            | none => simp [h, hu b]
            | some s => simpa [h] using hdual b s
      _ = (∑ b, u b) +
          (∑ b, match z'.assigned b with | none => 0 | some s => p s) := by
            rw [Finset.sum_add_distrib]
      _ ≤ (∑ b, u b) + (∑ s, p s) := by
            gcongr
            exact hprice z'
  have hprice_eq :
      (∑ b, match z.assigned b with | none => 0 | some s => p s) = ∑ s, p s := by
    rw [buyerMatching_sum_prices]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs with hs
    · rfl
    · simp [hunsold s hs]
  have hweight_eq : matchingWeight z q = (∑ b, u b) + (∑ s, p s) := by
    calc
      matchingWeight z q =
          ∑ b, (u b + match z.assigned b with | none => 0 | some s => p s) := by
            unfold matchingWeight
            apply Finset.sum_congr rfl
            intro b _
            cases h : z.assigned b with
            | none => simp [u, h]
            | some s => simp [u, h]
      _ = (∑ b, u b) +
          (∑ b, match z.assigned b with | none => 0 | some s => p s) := by
            rw [Finset.sum_add_distrib]
      _ = (∑ b, u b) + (∑ s, p s) := by rw [hprice_eq]
  intro z'
  rw [hweight_eq]
  exact hupper z'

/- Source: Scratch_PricingWithTips_one_new_store.lean -/

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D] [Nonempty D]

private noncomputable def newStoreCourier
    (A : Allocation B S D) (f : D ≃ D) (d : D) (s : S) : D := by
  classical
  exact if A.Sells s then f (soldStoreCourier A s) else d

private theorem newStoreCourier_sold
    (A : Allocation B S D) (f : D ≃ D) (d : D)
    {s : S} (hs : A.Sells s) :
    newStoreCourier A f d s = f (soldStoreCourier A s) := by
  simp [newStoreCourier, hs]

private theorem newStoreCourier_unsold
    (A : Allocation B S D) (f : D ≃ D) (d : D)
    {s : S} (hs : ¬ A.Sells s) :
    newStoreCourier A f d s = d := by
  simp [newStoreCourier, hs]

private noncomputable def singleNewStoreAllocation
    (A : Allocation B S D) (z : BuyerMatching B S)
    (snew : S)
    (honlynew : ∀ b s, z.assigned b = some s → ¬ A.Sells s → s = snew)
    (idle d : D) (hidle : ¬ A.CourierWorks idle)
    (f : D ≃ D) (hfidle : f idle = d) : Allocation B S D where
  assigned := fun b => (z.assigned b).map (fun s => (s,newStoreCourier A f d s))
  store_unique := by
    intro b₁ b₂ s e₁ e₂ h₁ h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨s₁,hz₁,hp₁⟩ := h₁
    obtain ⟨s₂,hz₂,hp₂⟩ := h₂
    have hs₁ : s₁ = s := congrArg Prod.fst hp₁
    have hs₂ : s₂ = s := congrArg Prod.fst hp₂
    exact z.store_unique (by simpa [hs₁] using hz₁) (by simpa [hs₂] using hz₂)
  courier_unique := by
    intro b₁ b₂ s₁ s₂ e h₁ h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨t₁,hz₁,hp₁⟩ := h₁
    obtain ⟨t₂,hz₂,hp₂⟩ := h₂
    have he₁ : newStoreCourier A f d t₁ = e := congrArg Prod.snd hp₁
    have he₂ : newStoreCourier A f d t₂ = e := congrArg Prod.snd hp₂
    by_cases hs₁ : A.Sells t₁ <;> by_cases hs₂ : A.Sells t₂
    · rw [newStoreCourier_sold A f d hs₁] at he₁
      rw [newStoreCourier_sold A f d hs₂] at he₂
      have hc : soldStoreCourier A t₁ = soldStoreCourier A t₂ :=
        f.injective (he₁.trans he₂.symm)
      have ht : t₁ = t₂ := soldStoreCourier_injective A hs₁ hs₂ hc
      subst t₂
      exact z.store_unique hz₁ hz₂
    · rw [newStoreCourier_sold A f d hs₁] at he₁
      rw [newStoreCourier_unsold A f d hs₂] at he₂
      have hid : soldStoreCourier A t₁ = idle :=
        f.injective ((he₁.trans he₂.symm).trans hfidle.symm)
      obtain ⟨b₀,ht⟩ := soldStoreCourier_trades A hs₁
      exact False.elim (hidle ⟨b₀,t₁,by simpa [hid] using ht⟩)
    · rw [newStoreCourier_unsold A f d hs₁] at he₁
      rw [newStoreCourier_sold A f d hs₂] at he₂
      have hid : soldStoreCourier A t₂ = idle :=
        f.injective ((he₂.trans he₁.symm).trans hfidle.symm)
      obtain ⟨b₀,ht⟩ := soldStoreCourier_trades A hs₂
      exact False.elim (hidle ⟨b₀,t₂,by simpa [hid] using ht⟩)
    · have ht₁ := honlynew b₁ t₁ hz₁ hs₁
      have ht₂ := honlynew b₂ t₂ hz₂ hs₂
      exact z.store_unique (by simpa [ht₁] using hz₁)
        (by simpa [ht₂] using hz₂)

private noncomputable def originalStoreReassignedCost
    (M : Market B S D) (A : Allocation B S D) (f : D ≃ D) (s : S) : ℝ := by
  classical
  exact if hs : A.Sells s then
    M.cost (f (soldStoreCourier A s)) (Classical.choose hs) s else 0

private theorem originalStoreReassignedCost_nonneg
    (M : Market B S D) (A : Allocation B S D) (f : D ≃ D) (s : S) :
    0 ≤ originalStoreReassignedCost M A f s := by
  classical
  unfold originalStoreReassignedCost
  split_ifs with hs
  · exact M.cost_nonneg _ _ _
  · exact le_refl _

private theorem originalStoreReassignedCost_eq_of_trade
    (M : Market B S D) (A : Allocation B S D) (f : D ≃ D)
    {b : B} {s : S} {d : D} (ht : A.Trades b s d) :
    originalStoreReassignedCost M A f s = M.cost (f d) b s := by
  classical
  have hs : A.Sells s := ⟨b,d,ht⟩
  have hchoose : A.Trades (Classical.choose hs) s
      (Classical.choose (Classical.choose_spec hs)) :=
    Classical.choose_spec (Classical.choose_spec hs)
  have hb : Classical.choose hs = b := A.store_unique hchoose ht
  simp only [originalStoreReassignedCost, dif_pos hs]
  rw [hb, soldStoreCourier_eq_of_trade A ht]

private theorem sum_originalStoreReassignedCost
    (M : Market B S D) (A : Allocation B S D) (f : D ≃ D) :
    (∑ b : B, match A.toBuyerMatching.assigned b with
      | none => (0 : ℝ)
      | some s => originalStoreReassignedCost M A f s) =
    ∑ b : B, match A.assigned b with
      | none => (0 : ℝ)
      | some (s,d) => M.cost (f d) b s := by
  classical
  apply Finset.sum_congr rfl
  intro b _
  cases ha : A.assigned b with
  | none => simp [Allocation.toBuyerMatching, ha]
  | some sd =>
    rcases sd with ⟨s,d⟩
    have ht : A.Trades b s d := ha
    simp [Allocation.toBuyerMatching, ha,
      originalStoreReassignedCost_eq_of_trade M A f ht]

private theorem sold_store_adjusted_gap_le_reassigned_cost
    (M : Market B S D) (A : Allocation B S D)
    (cBS : B → S → ℝ) (cDS : D → S → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDS d s)
    (w : B → S → ℝ) (uBar : D → ℝ)
    (hplan : IsCourierPlanFor M A w)
    (hreal : ∀ d, courierRealizedUtility M A w d = uBar d)
    (f : D ≃ D) (b : B) (s : S) (hs : A.Sells s) :
    adjustedValue M A uBar b s -
      (M.value b s - M.cost (f (soldStoreCourier A s)) b s) ≤
        originalStoreReassignedCost M A f s := by
  classical
  obtain ⟨b₀,ht₀⟩ := soldStoreCourier_trades A hs
  have hpcost := originalStoreReassignedCost_eq_of_trade M A f ht₀
  by_cases hd : A.Delivers b s
  · obtain ⟨e,ht⟩ := hd
    have he : soldStoreCourier A s = e := soldStoreCourier_eq_of_trade A ht
    have hb : b₀ = b := A.store_unique ht₀ ht
    have hd' : A.Delivers b s := ⟨e,ht⟩
    have hq : adjustedValue M A uBar b s = M.value b s := by
      simp [adjustedValue, requiredTip, hd']
    rw [hq, he]
    simpa [hb, he] using hpcost.symm.le
  · have hq := adjustedValue_sold_store_off_cost M A cBS cDS
      hcost w uBar hplan hreal b s hs hd
    have hn : 0 ≤ w b₀ s - M.cost (soldStoreCourier A s) b₀ s :=
      (hplan.2.1 (soldStoreCourier A s) b₀ s ht₀).1
    have hr := hreal (soldStoreCourier A s)
    rw [realized_eq_trade' M A w ht₀] at hr
    have hu : 0 ≤ uBar (soldStoreCourier A s) := by linarith
    have hdelta :
        M.cost (f (soldStoreCourier A s)) b s -
          M.cost (soldStoreCourier A s) b s =
        M.cost (f (soldStoreCourier A s)) b₀ s -
          M.cost (soldStoreCourier A s) b₀ s := by
      simp [hcost]
    rw [hq, hpcost]
    linarith [M.cost_nonneg (soldStoreCourier A s) b₀ s]

theorem toBuyerMatching_sells_iff
    (A : Allocation B S D) (s : S) :
    (∃ b, A.toBuyerMatching.assigned b = some s) ↔ A.Sells s := by
  constructor
  · rintro ⟨b,hb⟩
    simp only [Allocation.toBuyerMatching, Option.map_eq_some_iff] at hb
    obtain ⟨⟨t,d⟩,ha,ht⟩ := hb
    have hts : t = s := ht
    refine ⟨b,d,?_⟩
    change A.assigned b = some (s,d)
    simpa [hts] using ha
  · rintro ⟨b,d,ht⟩
    refine ⟨b,?_⟩
    change A.assigned b = some (s,d) at ht
    change (A.assigned b).map Prod.fst = some s
    rw [ht]
    rfl

theorem one_new_store_alternative_le
    (M : Market B S D) (A : Allocation B S D)
    (cBS : B → S → ℝ) (cDS : D → S → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDS d s)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar)
    (z : BuyerMatching B S) (bnew : B) (snew : S)
    (hnew : z.assigned bnew = some snew) (hunsold : ¬ A.Sells snew)
    (honlynew : ∀ b s, z.assigned b = some s → ¬ A.Sells s → s = snew) :
    matchingWeight z (adjustedValue M A uBar) ≤
      matchingWeight A.toBuyerMatching (adjustedValue M A uBar) := by
  classical
  obtain ⟨w,hplan,hreal⟩ := hu.1
  obtain ⟨d,hdmin⟩ :=
    exists_eq_ciInf_of_finite (f := fun d : D => M.cost d bnew snew + uBar d)
  obtain ⟨idle,hidle,hall⟩ :=
    maximalCourierUtility_ge_reassignment_cost_gap M A hoptimal hnotfull uBar hu
  obtain ⟨f,hfidle,hgap⟩ := hall d
  let A' := singleNewStoreAllocation A z snew honlynew idle d hidle f hfidle
  let p : S → ℝ := originalStoreReassignedCost M A f
  let q : B → S → ℝ := adjustedValue M A uBar
  have hp_nonneg : ∀ s, 0 ≤ p s := by
    intro s
    exact originalStoreReassignedCost_nonneg M A f s
  have hpoint : ∀ b,
      (match z.assigned b with
        | none => (0 : ℝ)
        | some s => q b s) -
      (match A'.assigned b with
        | none => (0 : ℝ)
        | some (s,e) => M.value b s - M.cost e b s) ≤
      (match z.assigned b with
        | none => (0 : ℝ)
        | some s => p s) -
      (if b = bnew then uBar d else 0) := by
    intro b
    by_cases hb : b = bnew
    · subst b
      have hoff : ¬ A.Delivers bnew snew := by
        rintro ⟨e,ht⟩
        exact hunsold ⟨bnew,e,ht⟩
      have hq : q bnew snew =
          M.value bnew snew - (M.cost d bnew snew + uBar d) := by
        simp only [q, adjustedValue, requiredTip, if_neg hoff]
        rw [hdmin]
      have hpzero : p snew = 0 := by
        simp [p, originalStoreReassignedCost, hunsold]
      simp only [hnew, A', singleNewStoreAllocation, Option.map_some,
        newStoreCourier_unsold A f d hunsold, if_true]
      rw [hq, hpzero]
      linarith
    · cases hz : z.assigned b with
      | none =>
          simp [A', singleNewStoreAllocation, hz, hb]
      | some s =>
          have hs : A.Sells s := by
            by_contra hns
            have he : s = snew := honlynew b s hz hns
            have hb' : b = bnew := z.store_unique (by simpa [he] using hz) hnew
            exact hb hb'
          have hqle := sold_store_adjusted_gap_le_reassigned_cost
            M A cBS cDS hcost w uBar hplan hreal f b s hs
          simp only [hz, A', singleNewStoreAllocation, Option.map_some,
            newStoreCourier_sold A f d hs, q, p, if_neg hb]
          simpa using hqle
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpoint b)
  simp only [Finset.sum_sub_distrib] at hsum
  have hsum' : matchingWeight z q - welfare M A' ≤
      (∑ b : B, match z.assigned b with
        | none => (0 : ℝ)
        | some s => p s) - uBar d := by
    have hsumite : (∑ x : B, if x = bnew then uBar d else 0) = uBar d := by
      simp
    rw [hsumite] at hsum
    change matchingWeight z q - welfare M A' ≤
      (∑ b : B, match z.assigned b with
        | none => (0 : ℝ)
        | some s => p s) - uBar d at hsum
    exact hsum
  have hpcomp : (∑ b : B, match z.assigned b with
        | none => (0 : ℝ)
        | some s => p s) ≤
      ∑ b : B, match A.toBuyerMatching.assigned b with
        | none => (0 : ℝ)
        | some s => p s := by
    calc
      _ = ∑ s : S, if ∃ b, z.assigned b = some s then p s else 0 := by
        convert buyerMatching_sum_prices z p using 1 <;> rfl
      _ ≤ ∑ s : S, if ∃ b, A.toBuyerMatching.assigned b = some s then p s else 0 := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : A.Sells s
        · rw [if_pos ((toBuyerMatching_sells_iff A s).2 hs)]
          split_ifs
          · exact le_refl _
          · exact hp_nonneg s
        · have hp0 : p s = 0 := by simp [p, originalStoreReassignedCost, hs]
          simp [hp0]
      _ = _ := by
        convert (buyerMatching_sum_prices A.toBuyerMatching p).symm using 1 <;> rfl
  have hpA := sum_originalStoreReassignedCost M A f
  have hqA : matchingWeight A.toBuyerMatching q =
      ∑ b : B, match A.assigned b with
        | none => (0 : ℝ)
        | some (s,_) => M.value b s := by
    unfold matchingWeight
    apply Finset.sum_congr rfl
    intro b _
    cases ha : A.assigned b with
    | none => simp [Allocation.toBuyerMatching, ha]
    | some sd =>
        rcases sd with ⟨s,e⟩
        have ht : A.Delivers b s := ⟨e,ha⟩
        simp [Allocation.toBuyerMatching, ha, q, adjustedValue, requiredTip, ht]
  have hWA : welfare M A =
      (∑ b : B, match A.assigned b with
        | none => (0 : ℝ)
        | some (s,_) => M.value b s) -
      (∑ b : B, match A.assigned b with
        | none => (0 : ℝ)
        | some (s,e) => M.cost e b s) := by
    unfold welfare
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    cases ha : A.assigned b with
    | none => simp [ha]
    | some sd => rcases sd with ⟨s,e⟩; simp [ha]
  have hopt := hoptimal A'
  have hmain := le_trans hsum' (sub_le_sub_right hpcomp (uBar d))
  rw [hpA] at hmain
  have hCid := sum_assigned_eq_sum_courierSlots A (fun e b s => M.cost e b s)
  have hCf := sum_assigned_eq_sum_courierSlots A (fun e b s => M.cost (f e) b s)
  have hgap' :
      (∑ b : B, match A.assigned b with
        | none => (0 : ℝ)
        | some (s,e) => M.cost (f e) b s) -
      (∑ b : B, match A.assigned b with
        | none => (0 : ℝ)
        | some (s,e) => M.cost e b s) ≤ uBar d := by
    calc
      _ = (∑ slot : D, match courierSlot A slot with
          | none => (0 : ℝ)
          | some (b,s) => M.cost (f slot) b s) -
          (∑ slot : D, match courierSlot A slot with
          | none => (0 : ℝ)
          | some (b,s) => M.cost slot b s) := by
          exact congrArg₂ (fun x y : ℝ => x - y)
            (by convert hCf using 1 <;> rfl)
            (by convert hCid using 1 <;> rfl)
      _ ≤ uBar d := hgap
  rw [hWA] at hopt
  change matchingWeight z q ≤ matchingWeight A.toBuyerMatching q
  rw [hqA]
  linarith

end PricingWithTips

/- Source: Scratch_PricingWithTips_matching_equivalence.lean -/

namespace PricingWithTips

open AssignmentGame.CoreCorners

variable {B S : Type*} [Fintype B] [Fintype S]
  [DecidableEq B] [DecidableEq S]

noncomputable def buyerPairs (z : BuyerMatching B S) : Finset (B × S) :=
  Finset.univ.filter (fun bs => z.assigned bs.1 = some bs.2)

theorem buyerPairs_matching (z : BuyerMatching B S) :
    IsMatching Finset.univ Finset.univ (buyerPairs z) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp
  · intro p hp q hq hfirst
    have hp' : z.assigned p.1 = some p.2 := (Finset.mem_filter.mp hp).2
    have hq' : z.assigned q.1 = some q.2 := (Finset.mem_filter.mp hq).2
    have hsecond : p.2 = q.2 := by
      have h : some p.2 = some q.2 := by
        calc
          some p.2 = z.assigned p.1 := hp'.symm
          _ = z.assigned q.1 := by rw [hfirst]
          _ = some q.2 := hq'
      exact Option.some.inj h
    exact Prod.ext hfirst hsecond
  · intro p hp q hq hsecond
    have hp' : z.assigned p.1 = some p.2 := (Finset.mem_filter.mp hp).2
    have hq' : z.assigned q.1 = some q.2 := (Finset.mem_filter.mp hq).2
    have hfirst : p.1 = q.1 := z.store_unique hp' (by simpa [hsecond] using hq')
    exact Prod.ext hfirst hsecond

theorem buyerPairs_weight (z : BuyerMatching B S) (a : B → S → ℝ) :
    (∑ bs ∈ buyerPairs z, a bs.1 bs.2) = matchingWeight z a := by
  classical
  simp only [buyerPairs, Finset.sum_filter, matchingWeight]
  rw [← Finset.univ_product_univ]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro b _
  cases h : z.assigned b with
  | none => simp [h]
  | some s => simp [h]

theorem buyerPairs_surjective
    (Q : Finset (B × S)) (hQ : IsMatching Finset.univ Finset.univ Q) :
    ∃ z : BuyerMatching B S, buyerPairs z = Q := by
  classical
  let z : BuyerMatching B S := {
    assigned := fun b => if h : ∃ s, (b, s) ∈ Q then some (Classical.choose h) else none
    store_unique := by
      intro b₁ b₂ s h₁ h₂
      have he₁ : ∃ s, (b₁, s) ∈ Q := by
        by_contra hn
        simp [hn] at h₁
      have he₂ : ∃ s, (b₂, s) ∈ Q := by
        by_contra hn
        simp [hn] at h₂
      have hc₁ : (b₁, Classical.choose he₁) ∈ Q := Classical.choose_spec he₁
      have hc₂ : (b₂, Classical.choose he₂) ∈ Q := Classical.choose_spec he₂
      have hs₁ : Classical.choose he₁ = s := by
        have h := h₁
        simp only [dif_pos he₁] at h
        exact Option.some.inj h
      have hs₂ : Classical.choose he₂ = s := by
        have h := h₂
        simp only [dif_pos he₂] at h
        exact Option.some.inj h
      have hpair := hQ.2.2 (b₁, s) (by simpa [hs₁] using hc₁)
        (b₂, s) (by simpa [hs₂] using hc₂) rfl
      exact congrArg Prod.fst hpair
  }
  refine ⟨z, ?_⟩
  ext bs
  rcases bs with ⟨b, s⟩
  simp only [buyerPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hassign
    have he : ∃ s, (b, s) ∈ Q := by
      by_contra hn
      simp [z, hn] at hassign
    have hc : (b, Classical.choose he) ∈ Q := Classical.choose_spec he
    have hs : Classical.choose he = s := by
      simp only [z, dif_pos he] at hassign
      exact Option.some.inj hassign
    simpa [hs] using hc
  · intro hmem
    have he : ∃ s, (b, s) ∈ Q := ⟨s, hmem⟩
    have hc : (b, Classical.choose he) ∈ Q := Classical.choose_spec he
    have hp := hQ.2.1 (b, Classical.choose he) hc (b, s) hmem rfl
    have hs : Classical.choose he = s := congrArg Prod.snd hp
    simp [z, he, hs]

end PricingWithTips

/- Source: Scratch_PricingWithTips_worth_matching_bridge.lean -/

namespace PricingWithTips

open AssignmentGame.CoreCorners

variable {B S : Type*} [Fintype B] [Fintype S]
  [DecidableEq B] [DecidableEq S]

theorem matchingWeight_le_worth_max_zero
    (z : BuyerMatching B S) (q : B → S → ℝ) :
    matchingWeight z q ≤
      worth (fun b s => max 0 (q b s)) Finset.univ Finset.univ := by
  classical
  have hP := buyerPairs_matching z
  have hle := ag1171_le_worth (fun b s => max 0 (q b s)) hP
  rw [← buyerPairs_weight z q]
  calc
    (∑ bs ∈ buyerPairs z, q bs.1 bs.2) ≤
        ∑ bs ∈ buyerPairs z, max 0 (q bs.1 bs.2) :=
      Finset.sum_le_sum (fun bs _ => le_max_right _ _)
    _ ≤ _ := hle

theorem worth_max_zero_le_of_matching_bound
    (q : B → S → ℝ) (A : Finset B) (T : Finset S) (C : ℝ)
    (hbound : ∀ z : BuyerMatching B S,
      (∀ b s, z.assigned b = some s → b ∈ A ∧ s ∈ T) →
      matchingWeight z q ≤ C) :
    worth (fun b s => max 0 (q b s)) A T ≤ C := by
  classical
  obtain ⟨P,hP,hW⟩ :=
    ag1171_exists_opt (fun b s => max 0 (q b s)) A T
  let R : Finset (B × S) := P.filter (fun bs => 0 < q bs.1 bs.2)
  have hR : IsMatching A T R := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      exact hP.1 (Finset.mem_filter.1 hp).1
    · intro p hp r hr he
      exact hP.2.1 p (Finset.mem_filter.1 hp).1 r (Finset.mem_filter.1 hr).1 he
    · intro p hp r hr he
      exact hP.2.2 p (Finset.mem_filter.1 hp).1 r (Finset.mem_filter.1 hr).1 he
  have hweight : (∑ bs ∈ R, q bs.1 bs.2) =
      ∑ bs ∈ P, max 0 (q bs.1 bs.2) := by
    simp only [R, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro bs _
    by_cases hpos : 0 < q bs.1 bs.2
    · simp [hpos, max_eq_right (le_of_lt hpos)]
    · have hnonpos : q bs.1 bs.2 ≤ 0 := le_of_not_gt hpos
      simp [hpos, max_eq_left hnonpos]
  obtain ⟨z,hz⟩ := buyerPairs_surjective R
    (by
      refine ⟨?_,hR.2.1,hR.2.2⟩
      intro p hp
      exact Finset.mem_product.2 ⟨Finset.mem_univ _,Finset.mem_univ _⟩)
  have hzsubset : ∀ b s, z.assigned b = some s → b ∈ A ∧ s ∈ T := by
    intro b s hzs
    have hm : (b,s) ∈ buyerPairs z := by
      simp [buyerPairs, hzs]
    rw [hz] at hm
    exact Finset.mem_product.1 (hR.1 hm)
  rw [hW, ← hweight, ← hz]
  rw [buyerPairs_weight]
  exact hbound z hzsubset

end PricingWithTips

/- Source: Scratch_AssignmentGame_buyer_marginal.lean -/

namespace AssignmentGame.CoreCorners

set_option autoImplicit false

private theorem matching_swap
    {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    {A : Finset M} {B : Finset N} {P : Finset (M × N)}
    (hP : IsMatching A B P) :
    IsMatching B A (P.image Prod.swap) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.1 hq
    have hm := Finset.mem_product.1 (hP.1 hp)
    exact Finset.mem_product.2 ⟨hm.2,hm.1⟩
  · intro p hp q hq he
    obtain ⟨p₀,hp₀,rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨q₀,hq₀,rfl⟩ := Finset.mem_image.1 hq
    have hpq : p₀ = q₀ := hP.2.2 p₀ hp₀ q₀ hq₀ he
    rw [hpq]
  · intro p hp q hq he
    obtain ⟨p₀,hp₀,rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨q₀,hq₀,rfl⟩ := Finset.mem_image.1 hq
    have hpq : p₀ = q₀ := hP.2.1 p₀ hp₀ q₀ hq₀ he
    rw [hpq]

private theorem sum_swap
    {M N : Type*} [DecidableEq M] [DecidableEq N]
    (a : M → N → ℝ) (P : Finset (M × N)) :
    (∑ q ∈ P.image Prod.swap, a q.2 q.1) =
      ∑ p ∈ P, a p.1 p.2 := by
  classical
  rw [Finset.sum_image]
  · simp
  · intro p hp q hq he
    have h := congrArg Prod.swap he
    simpa using h

private theorem worth_transpose_le
    {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (a : M → N → ℝ) (A : Finset M) (B : Finset N) :
    worth a A B ≤ worth (fun j i => a i j) B A := by
  classical
  obtain ⟨P,hP,hW⟩ := ag1171_exists_opt a A B
  rw [hW]
  calc
    (∑ p ∈ P, a p.1 p.2) =
        ∑ q ∈ P.image Prod.swap, a q.2 q.1 := (sum_swap a P).symm
    _ ≤ worth (fun j i => a i j) B A :=
      ag1171_le_worth (fun j i => a i j) (matching_swap hP)

theorem worth_transpose
    {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (a : M → N → ℝ) (A : Finset M) (B : Finset N) :
    worth a A B = worth (fun j i => a i j) B A := by
  apply le_antisymm
  · exact worth_transpose_le a A B
  · exact worth_transpose_le (fun j i => a i j) B A

theorem core_swap
    {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (a : M → N → ℝ) {u : M → ℝ} {v : N → ℝ}
    (h : (u,v) ∈ core a) :
    (v,u) ∈ core (fun j i => a i j) := by
  constructor
  · have ht := h.1
    rw [worth_transpose a Finset.univ Finset.univ] at ht
    simpa [add_comm] using ht
  · intro B A
    have ht := h.2 A B
    rw [worth_transpose a A B] at ht
    simpa [add_comm] using ht

theorem uHi_eq_transpose_vHi
    {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (a : M → N → ℝ) (i : M) :
    uHi a i = vHi (fun j i => a i j) i := by
  unfold uHi vHi
  congr 1
  ext x
  constructor
  · rintro ⟨⟨u,v⟩,h,rfl⟩
    exact ⟨(v,u),core_swap a h,rfl⟩
  · rintro ⟨⟨v,u⟩,h,rfl⟩
    exact ⟨(u,v),core_swap (fun j i => a i j) h,rfl⟩

theorem uHi_eq_removal_loss
    {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j) (i : M) :
    uHi a i = worth a Finset.univ Finset.univ -
      worth a (Finset.univ.erase i) Finset.univ := by
  rw [uHi_eq_transpose_vHi]
  rw [vHi_eq_removal_loss (fun j i => a i j) (fun j i => ha i j) i]
  rw [← worth_transpose a Finset.univ Finset.univ]
  rw [← worth_transpose a (Finset.univ.erase i) Finset.univ]

end AssignmentGame.CoreCorners

/- Source: Scratch_AssignmentGame_single_new_suffices.lean -/

namespace AssignmentGame.CoreCorners

set_option autoImplicit false

theorem worth_zero_outside_eq_restricted
    {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (a : M → N → ℝ) (T : Finset N) :
    worth (fun i j => if j ∈ T then a i j else 0)
      Finset.univ Finset.univ = worth a Finset.univ T := by
  classical
  let aT : M → N → ℝ := fun i j => if j ∈ T then a i j else 0
  apply le_antisymm
  · obtain ⟨P,hP,hW⟩ := ag1171_exists_opt aT Finset.univ Finset.univ
    let R : Finset (M × N) := P.filter (fun p => p.2 ∈ T)
    have hR : IsMatching (Finset.univ : Finset M) T R := by
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        exact Finset.mem_product.2 ⟨Finset.mem_univ _,(Finset.mem_filter.1 hp).2⟩
      · intro p hp q hq he
        exact hP.2.1 p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 he
      · intro p hp q hq he
        exact hP.2.2 p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 he
    have hweight : (∑ p ∈ R, a p.1 p.2) = ∑ p ∈ P, aT p.1 p.2 := by
      simp only [R, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p.2 ∈ T <;> simp [hp, aT]
    change worth aT Finset.univ Finset.univ ≤ worth a Finset.univ T
    rw [hW, ← hweight]
    exact ag1171_le_worth a hR
  · obtain ⟨P,hP,hW⟩ := ag1171_exists_opt a Finset.univ T
    have hPfull : IsMatching (Finset.univ : Finset M) (Finset.univ : Finset N) P := by
      refine ⟨?_,hP.2.1,hP.2.2⟩
      intro p hp
      exact Finset.mem_product.2 ⟨Finset.mem_univ _,Finset.mem_univ _⟩
    have hweight : (∑ p ∈ P, aT p.1 p.2) = ∑ p ∈ P, a p.1 p.2 := by
      apply Finset.sum_congr rfl
      intro p hp
      have ht := (Finset.mem_product.1 (hP.1 hp)).2
      simp [aT, ht]
    change worth a Finset.univ T ≤ worth aT Finset.univ Finset.univ
    rw [hW, ← hweight]
    exact ag1171_le_worth aT hPfull

theorem worth_full_le_of_no_single_new_gain
    {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (T : Finset N)
    (hnew : ∀ s : N, s ∉ T →
      worth a Finset.univ (insert s T) ≤
        worth (fun i j => if j ∈ T then a i j else 0)
          Finset.univ Finset.univ) :
    worth a Finset.univ Finset.univ ≤
      worth (fun i j => if j ∈ T then a i j else 0)
        Finset.univ Finset.univ := by
  classical
  let aT : M → N → ℝ := fun i j => if j ∈ T then a i j else 0
  have haT : ∀ i j, 0 ≤ aT i j := by
    intro i j
    by_cases hj : j ∈ T
    · simpa [aT, hj] using ha i j
    · simp [aT, hj]
  let aFlip : N → M → ℝ := fun j i => aT i j
  let u : M → ℝ := vHi aFlip
  let v : N → ℝ := uLo aFlip
  have hcoreT : (v,u) ∈ core aFlip :=
    (core_corners_accepted aFlip (fun j i => haT i j)).1
  have hcore : (u,v) ∈ core aT := by
    simpa only [aFlip] using core_swap aFlip hcoreT
  have hdf := (ag1171_core_iff aT u v).1 hcore
  have hu : ∀ i, 0 ≤ u i := hdf.1.1
  have hv : ∀ j, 0 ≤ v j := hdf.1.2.1
  have hdualT : ∀ i j, aT i j ≤ u i + v j := hdf.1.2.2
  have hsum : (∑ i : M, u i) + (∑ j : N, v j) =
      worth aT Finset.univ Finset.univ := hdf.2
  have hvzero : ∀ j, j ∉ T → v j = 0 := by
    intro j hj
    have h := hcore.2 Finset.univ (Finset.univ.erase j)
    have hnonneg := hv j
    -- Since aT has a zero column at j, any optimal matching can omit j.
    have heq : worth aT Finset.univ Finset.univ =
        worth aT Finset.univ (Finset.univ.erase j) := by
      obtain ⟨P,hP,hW⟩ := ag1171_exists_opt aT Finset.univ Finset.univ
      let R := P.filter (fun p => p.2 ≠ j)
      have hR : IsMatching (Finset.univ : Finset M) (Finset.univ.erase j) R := by
        refine ⟨?_, ?_, ?_⟩
        · intro p hp
          exact Finset.mem_product.2 ⟨Finset.mem_univ _,
            Finset.mem_erase.2 ⟨(Finset.mem_filter.1 hp).2, Finset.mem_univ _⟩⟩
        · intro p hp q hq he
          exact hP.2.1 p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 he
        · intro p hp q hq he
          exact hP.2.2 p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 he
      have hweight : (∑ p ∈ R, aT p.1 p.2) = ∑ p ∈ P, aT p.1 p.2 := by
        simp only [R, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hpj : p.2 = j
        · simp [hpj, aT, hj]
        · simp [hpj]
      apply le_antisymm
      · rw [hW, ← hweight]
        exact ag1171_le_worth aT hR
      · obtain ⟨Q,hQ,hQW⟩ :=
          ag1171_exists_opt aT Finset.univ (Finset.univ.erase j)
        have hQfull : IsMatching (Finset.univ : Finset M) (Finset.univ : Finset N) Q := by
          refine ⟨?_,hQ.2.1,hQ.2.2⟩
          intro p hp
          exact Finset.mem_product.2 ⟨Finset.mem_univ _,Finset.mem_univ _⟩
        rw [hQW]
        exact ag1171_le_worth aT hQfull
    have hsumj : (∑ k ∈ (Finset.univ : Finset N).erase j, v k) + v j =
        ∑ k : N, v k := Finset.sum_erase_add _ _ (Finset.mem_univ j)
    rw [← heq] at h
    change worth aT Finset.univ Finset.univ ≤
      (∑ i : M, u i) + ∑ k ∈ (Finset.univ : Finset N).erase j, v k at h
    rw [← hsum] at h
    linarith
  have hdual : ∀ i j, a i j ≤ u i + v j := by
    intro i j
    by_cases hj : j ∈ T
    · simpa only [aT, if_pos hj] using hdualT i j
    · have hub : a i j ≤ u i := by
        obtain ⟨P,hP,hW⟩ :=
          ag1171_exists_opt aT ((Finset.univ : Finset M).erase i) Finset.univ
        let R : Finset (M × N) := P.filter (fun p => p.2 ∈ T)
        have hR : IsMatching ((Finset.univ : Finset M).erase i) T R := by
          refine ⟨?_, ?_, ?_⟩
          · intro p hp
            have hpP := (Finset.mem_filter.1 hp).1
            have hpT := (Finset.mem_filter.1 hp).2
            exact Finset.mem_product.2 ⟨(Finset.mem_product.1 (hP.1 hpP)).1,hpT⟩
          · intro p hp q hq he
            exact hP.2.1 p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 he
          · intro p hp q hq he
            exact hP.2.2 p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 he
        have hRweight : (∑ p ∈ R, a p.1 p.2) =
            worth aT ((Finset.univ : Finset M).erase i) Finset.univ := by
          rw [hW]
          simp only [R, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro p hp
          by_cases hpT : p.2 ∈ T
          · simp [aT, hpT]
          · simp [aT, hpT]
        let Q : Finset (M × N) := insert (i,j) R
        have hQ : IsMatching (Finset.univ : Finset M) (insert j T) Q := by
          refine ⟨?_, ?_, ?_⟩
          · intro p hp
            rcases Finset.mem_insert.1 hp with rfl | hp
            · exact Finset.mem_product.2 ⟨Finset.mem_univ _,Finset.mem_insert_self _ _⟩
            · have hpT := Finset.mem_product.1 (hR.1 hp)
              exact Finset.mem_product.2 ⟨Finset.mem_univ _,Finset.mem_insert_of_mem hpT.2⟩
          · intro p hp q hq he
            rcases Finset.mem_insert.1 hp with rfl | hp
            · rcases Finset.mem_insert.1 hq with rfl | hq
              · rfl
              · exact False.elim ((Finset.mem_erase.1 (Finset.mem_product.1 (hR.1 hq)).1).1 he.symm)
            · rcases Finset.mem_insert.1 hq with rfl | hq
              · exact False.elim ((Finset.mem_erase.1 (Finset.mem_product.1 (hR.1 hp)).1).1 he)
              · exact hR.2.1 p hp q hq he
          · intro p hp q hq he
            rcases Finset.mem_insert.1 hp with rfl | hp
            · rcases Finset.mem_insert.1 hq with rfl | hq
              · rfl
              · have hqmem := (Finset.mem_product.1 (hR.1 hq)).2
                rw [← he] at hqmem
                exact False.elim (hj hqmem)
            · rcases Finset.mem_insert.1 hq with rfl | hq
              · have hpmem := (Finset.mem_product.1 (hR.1 hp)).2
                rw [he] at hpmem
                exact False.elim (hj hpmem)
              · exact hR.2.2 p hp q hq he
        have hQweight : (∑ p ∈ Q, a p.1 p.2) =
            a i j + worth aT ((Finset.univ : Finset M).erase i) Finset.univ := by
          have hnot : (i,j) ∉ R := by
            intro hm
            exact hj (Finset.mem_product.1 (hR.1 hm)).2
          rw [Finset.sum_insert hnot, hRweight]
        have hle := ag1171_le_worth a hQ
        rw [hQweight] at hle
        have hnewj := hnew j hj
        have hmargin : u i = worth aT Finset.univ Finset.univ -
            worth aT ((Finset.univ : Finset M).erase i) Finset.univ := by
          change vHi aFlip i = _
          rw [← uHi_eq_transpose_vHi aT i]
          exact uHi_eq_removal_loss aT haT i
        linarith
      rw [hvzero j hj]
      linarith
  have hdfull : ag1171_DF a u v := ⟨hu,hv,hdual⟩
  calc
    worth a Finset.univ Finset.univ ≤ (∑ i : M, u i) + ∑ j : N, v j := by
      apply ag1171_worth_le
      intro P hP
      exact ag1171_matching_sum_le a u v hdfull hP
    _ = worth aT Finset.univ Finset.univ := hsum

end AssignmentGame.CoreCorners

/- Source: Scratch_PricingWithTips_store_global.lean -/

namespace PricingWithTips

open AssignmentGame.CoreCorners

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]
  [Nonempty B] [Nonempty S] [Nonempty D]

theorem store_structured_adjusted_matching_global
    (M : Market B S D) (A : Allocation B S D)
    (cBS : B → S → ℝ) (cDS : D → S → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDS d s)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar) :
    IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by
  classical
  let T : Finset S := Finset.univ.filter A.Sells
  let q : B → S → ℝ := adjustedValue M A uBar
  let a : B → S → ℝ := fun b s => max 0 (q b s)
  let aT : B → S → ℝ := fun b s => if s ∈ T then a b s else 0
  have ha : ∀ b s, 0 ≤ a b s := by
    intro b s
    exact le_max_left _ _
  have hT : ∀ s, s ∈ T ↔ A.Sells s := by
    intro s
    simp [T]
  have hqa : ∀ b s, A.toBuyerMatching.assigned b = some s → 0 ≤ q b s := by
    intro b s hbs
    simp only [Allocation.toBuyerMatching, Option.map_eq_some_iff] at hbs
    obtain ⟨⟨t,d⟩,ht,he⟩ := hbs
    have hts : t = s := he
    have htrade : A.Trades b s d := by
      change A.assigned b = some (s,d)
      simpa [hts] using ht
    have hd : A.Delivers b s := ⟨d,htrade⟩
    have hq : q b s = M.value b s := by
      simp [q, adjustedValue, requiredTip, hd]
    rw [hq]
    exact M.value_nonneg b s
  have hWupper : worth aT Finset.univ Finset.univ ≤
      matchingWeight A.toBuyerMatching q := by
    change worth (fun b s => if s ∈ T then max 0 (q b s) else 0)
      Finset.univ Finset.univ ≤ matchingWeight A.toBuyerMatching q
    rw [worth_zero_outside_eq_restricted (fun b s => max 0 (q b s)) T]
    apply worth_max_zero_le_of_matching_bound q Finset.univ T _
    intro z hzsub
    apply sold_store_alternatives_le M A cBS cDS hcost hoptimal uBar hu z
    intro b s hzs
    exact (hT s).1 (hzsub b s hzs).2
  have hWlower : matchingWeight A.toBuyerMatching q ≤
      worth aT Finset.univ Finset.univ := by
    let P := buyerPairs A.toBuyerMatching
    have hP₀ := buyerPairs_matching A.toBuyerMatching
    have hP : IsMatching (Finset.univ : Finset B) T P := by
      refine ⟨?_,hP₀.2.1,hP₀.2.2⟩
      intro p hp
      have hzs : A.toBuyerMatching.assigned p.1 = some p.2 := by
        simpa [P, buyerPairs] using hp
      have hs : A.Sells p.2 :=
        (toBuyerMatching_sells_iff A p.2).1 ⟨p.1,hzs⟩
      exact Finset.mem_product.2 ⟨Finset.mem_univ _,(hT p.2).2 hs⟩
    have hweight : (∑ p ∈ P, aT p.1 p.2) =
        matchingWeight A.toBuyerMatching q := by
      rw [← buyerPairs_weight A.toBuyerMatching q]
      apply Finset.sum_congr rfl
      intro p hp
      have hzs : A.toBuyerMatching.assigned p.1 = some p.2 := by
        simpa [P, buyerPairs] using hp
      have hs : p.2 ∈ T := (Finset.mem_product.1 (hP.1 hp)).2
      simp [aT, a, hs, max_eq_right (hqa p.1 p.2 hzs)]
    rw [← hweight]
    exact ag1171_le_worth aT hP₀
  have hW : worth aT Finset.univ Finset.univ =
      matchingWeight A.toBuyerMatching q := le_antisymm hWupper hWlower
  have hsingle : ∀ s : S, s ∉ T →
      worth a Finset.univ (insert s T) ≤
        worth aT Finset.univ Finset.univ := by
    intro s hsnot
    have hsunsold : ¬ A.Sells s := by
      intro hs
      exact hsnot ((hT s).2 hs)
    rw [hW]
    change worth (fun b t => max 0 (q b t)) Finset.univ (insert s T) ≤
      matchingWeight A.toBuyerMatching q
    apply worth_max_zero_le_of_matching_bound q Finset.univ (insert s T) _
    intro z hzsub
    by_cases hzs : ∃ b, z.assigned b = some s
    · obtain ⟨bnew,hnew⟩ := hzs
      apply one_new_store_alternative_le M A cBS cDS hcost hoptimal hnotfull
        uBar hu z bnew s hnew hsunsold
      intro b t hzt htunsold
      have hmem : t ∈ insert s T := (hzsub b t hzt).2
      rcases Finset.mem_insert.1 hmem with h | h
      · exact h
      · exact False.elim (htunsold ((hT t).1 h))
    · apply sold_store_alternatives_le M A cBS cDS hcost hoptimal uBar hu z
      intro b t hzt
      have hmem : t ∈ insert s T := (hzsub b t hzt).2
      rcases Finset.mem_insert.1 hmem with h | h
      · exact False.elim (hzs ⟨b,by simpa [h] using hzt⟩)
      · exact (hT t).1 h
  have hfull : worth a Finset.univ Finset.univ ≤
      worth aT Finset.univ Finset.univ :=
    worth_full_le_of_no_single_new_gain a ha T hsingle
  intro z
  simpa only [q] using
    (matchingWeight_le_worth_max_zero z q).trans (hfull.trans hW.le)

end PricingWithTips

/- Source: Scratch_PricingWithTips_courier_slots.lean -/

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

noncomputable def courierSlot (A : Allocation B S D) (d : D) :
    Option (B × S) := by
  classical
  exact if h : A.CourierWorks d then
    some (Classical.choose h, Classical.choose (Classical.choose_spec h))
  else none

theorem courierSlot_eq_some_of_trade
    (A : Allocation B S D) {b : B} {s : S} {d : D}
    (ht : A.Trades b s d) : courierSlot A d = some (b,s) := by
  classical
  have hwork : A.CourierWorks d := ⟨b,s,ht⟩
  unfold courierSlot
  rw [dif_pos hwork]
  let b₀ := Classical.choose hwork
  let hs := Classical.choose_spec hwork
  let s₀ := Classical.choose hs
  have ht₀ : A.Trades b₀ s₀ d := Classical.choose_spec hs
  have hb : b₀ = b := A.courier_unique ht₀ ht
  have ht₀' : A.Trades b s₀ d := by simpa only [hb] using ht₀
  have hpair : (s₀,d) = (s,d) := Option.some.inj (ht₀'.symm.trans ht)
  have hss : s₀ = s := congrArg Prod.fst hpair
  change some (b₀,s₀) = some (b,s)
  rw [hb,hss]

private theorem courierSlot_trade_of_eq_some
    (A : Allocation B S D) {b : B} {s : S} {d : D}
    (hslot : courierSlot A d = some (b,s)) : A.Trades b s d := by
  classical
  by_cases hwork : A.CourierWorks d
  · obtain ⟨b₀,s₀,ht⟩ := hwork
    rw [courierSlot_eq_some_of_trade A ht] at hslot
    have hp : (b₀,s₀) = (b,s) := Option.some.inj hslot
    cases hp
    exact ht
  · simp [courierSlot, hwork] at hslot

theorem courierSlot_none_iff_idle
    (A : Allocation B S D) (d : D) :
    courierSlot A d = none ↔ ¬ A.CourierWorks d := by
  classical
  constructor
  · intro h hwork
    obtain ⟨b,s,ht⟩ := hwork
    rw [courierSlot_eq_some_of_trade A ht] at h
    contradiction
  · intro h
    simp [courierSlot, h]

theorem sum_assigned_eq_sum_courierSlots
    (A : Allocation B S D) (F : D → B → S → ℝ) :
    (∑ b, match A.assigned b with
      | none => 0
      | some (s,d) => F d b s) =
    ∑ d, match courierSlot A d with
      | none => 0
      | some (b,s) => F d b s := by
  classical
  let T : Finset B := Finset.univ.filter (fun b => (A.assigned b).isSome)
  let U : Finset D := Finset.univ.filter (fun d => A.CourierWorks d)
  let G : B → ℝ := fun b => match A.assigned b with
    | none => 0
    | some (s,d) => F d b s
  let H : D → ℝ := fun d => match courierSlot A d with
    | none => 0
    | some (b,s) => F d b s
  have hfilterB : (∑ b, G b) = ∑ b ∈ T, G b := by
    simp only [T, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    cases h : A.assigned b with
    | none => simp [G, h]
    | some sd => simp [G, h]
  have hfilterD : (∑ d, H d) = ∑ d ∈ U, H d := by
    simp only [U, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : A.CourierWorks d
    · simp [hd]
    · simp [H, (courierSlot_none_iff_idle A d).2 hd, hd]
  have hbij : (∑ d ∈ U, H d) = ∑ b ∈ T, G b := by
    apply Finset.sum_bij (fun d hd => Classical.choose
      (show A.CourierWorks d from (Finset.mem_filter.mp hd).2))
    · intro d hd
      have hwork : A.CourierWorks d := (Finset.mem_filter.mp hd).2
      let b₀ := Classical.choose hwork
      let hs := Classical.choose_spec hwork
      let s₀ := Classical.choose hs
      have ht : A.Trades b₀ s₀ d := Classical.choose_spec hs
      change A.assigned b₀ = some (s₀,d) at ht
      change b₀ ∈ T
      simp [T, ht]
    · intro d₁ hd₁ d₂ hd₂ hb
      have hw₁ : A.CourierWorks d₁ := (Finset.mem_filter.mp hd₁).2
      have hw₂ : A.CourierWorks d₂ := (Finset.mem_filter.mp hd₂).2
      let b₁ := Classical.choose hw₁
      let hs₁ := Classical.choose_spec hw₁
      let s₁ := Classical.choose hs₁
      have ht₁ : A.Trades b₁ s₁ d₁ := Classical.choose_spec hs₁
      let b₂ := Classical.choose hw₂
      let hs₂ := Classical.choose_spec hw₂
      let s₂ := Classical.choose hs₂
      have ht₂ : A.Trades b₂ s₂ d₂ := Classical.choose_spec hs₂
      change b₁ = b₂ at hb
      have ht₁' : A.Trades b₂ s₁ d₁ := by rw [← hb]; exact ht₁
      have hp : some (s₁,d₁) = some (s₂,d₂) := ht₁'.symm.trans ht₂
      exact congrArg Prod.snd (Option.some.inj hp)
    · intro b hb
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      cases h : A.assigned b with
      | none => simp [h] at hb
      | some sd =>
          rcases sd with ⟨s,d⟩
          have ht : A.Trades b s d := h
          have hw : A.CourierWorks d := ⟨b,s,ht⟩
          have hd : d ∈ U := by simp [U,hw]
          refine ⟨d,hd,?_⟩
          let b₀ := Classical.choose hw
          let hs := Classical.choose_spec hw
          let s₀ := Classical.choose hs
          have ht₀ : A.Trades b₀ s₀ d := Classical.choose_spec hs
          exact A.courier_unique ht₀ ht
    · intro d hd
      have hw : A.CourierWorks d := (Finset.mem_filter.mp hd).2
      let b₀ := Classical.choose hw
      let hs := Classical.choose_spec hw
      let s₀ := Classical.choose hs
      have ht : A.Trades b₀ s₀ d := Classical.choose_spec hs
      change A.assigned b₀ = some (s₀,d) at ht
      have hslot : courierSlot A d = some (b₀,s₀) :=
        courierSlot_eq_some_of_trade A ht
      change H d = G b₀
      simp [H,G,hslot,ht]
  simpa only [G,H] using hfilterB.trans (hbij.symm.trans hfilterD.symm)

end PricingWithTips

/- Source: Scratch_PricingWithTips_transpose.lean -/

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

def transposeMarket (M : Market B S D) : Market S B D where
  value s b := M.value b s
  cost d s b := M.cost d b s
  value_nonneg s b := M.value_nonneg b s
  cost_nonneg d s b := M.cost_nonneg d b s

private noncomputable def transposeAssigned
    (A : Allocation B S D) (s : S) : Option (B × D) := by
  classical
  exact if hs : A.Sells s then
    some (Classical.choose hs, Classical.choose (Classical.choose_spec hs)) else none

private theorem transposeAssigned_iff
    (A : Allocation B S D) (s : S) (b : B) (d : D) :
    transposeAssigned A s = some (b,d) ↔ A.Trades b s d := by
  classical
  constructor
  · intro h
    have hs : A.Sells s := by
      by_contra hn
      simp [transposeAssigned, hn] at h
    have hchoice : A.Trades (Classical.choose hs) s
        (Classical.choose (Classical.choose_spec hs)) :=
      Classical.choose_spec (Classical.choose_spec hs)
    simp only [transposeAssigned, dif_pos hs] at h
    have hp : (Classical.choose hs,
      Classical.choose (Classical.choose_spec hs)) = (b,d) := Option.some.inj h
    have hb : Classical.choose hs = b := congrArg Prod.fst hp
    have hd : Classical.choose (Classical.choose_spec hs) = d := congrArg Prod.snd hp
    change A.assigned b = some (s,d)
    calc
      A.assigned b = A.assigned (Classical.choose hs) :=
        (congrArg A.assigned hb).symm
      _ = some (s, Classical.choose (Classical.choose_spec hs)) := hchoice
      _ = some (s,d) := congrArg (fun e => some (s,e)) hd
  · intro ht
    have hs : A.Sells s := ⟨b,d,ht⟩
    have hchoice : A.Trades (Classical.choose hs) s
        (Classical.choose (Classical.choose_spec hs)) :=
      Classical.choose_spec (Classical.choose_spec hs)
    have hb : Classical.choose hs = b := A.store_unique hchoice ht
    have hchoice' : A.Trades b s
        (Classical.choose (Classical.choose_spec hs)) := by simpa [hb] using hchoice
    have hp : some (s,Classical.choose (Classical.choose_spec hs)) = some (s,d) :=
      hchoice'.symm.trans ht
    have hd : Classical.choose (Classical.choose_spec hs) = d :=
      congrArg Prod.snd (Option.some.inj hp)
    unfold transposeAssigned
    rw [dif_pos hs]
    exact congrArg some (Prod.ext hb hd)

noncomputable def transposeAllocation (A : Allocation B S D) : Allocation S B D where
  assigned := transposeAssigned A
  store_unique := by
    intro s₁ s₂ b d₁ d₂ h₁ h₂
    have ht₁ : A.Trades b s₁ d₁ := (transposeAssigned_iff A s₁ b d₁).1 h₁
    have ht₂ : A.Trades b s₂ d₂ := (transposeAssigned_iff A s₂ b d₂).1 h₂
    have hp : (s₁,d₁) = (s₂,d₂) := Option.some.inj (ht₁.symm.trans ht₂)
    exact congrArg Prod.fst hp
  courier_unique := by
    intro s₁ s₂ b₁ b₂ d h₁ h₂
    have ht₁ : A.Trades b₁ s₁ d := (transposeAssigned_iff A s₁ b₁ d).1 h₁
    have ht₂ : A.Trades b₂ s₂ d := (transposeAssigned_iff A s₂ b₂ d).1 h₂
    have hb : b₁ = b₂ := A.courier_unique ht₁ ht₂
    have ht₁' : A.Trades b₂ s₁ d := by simpa [hb] using ht₁
    have hp : (s₁,d) = (s₂,d) := Option.some.inj (ht₁'.symm.trans ht₂)
    exact congrArg Prod.fst hp

theorem transposeAllocation_trades
    (A : Allocation B S D) (b : B) (s : S) (d : D) :
    (transposeAllocation A).Trades s b d ↔ A.Trades b s d :=
  transposeAssigned_iff A s b d

theorem transposeAllocation_works
    (A : Allocation B S D) (d : D) :
    (transposeAllocation A).CourierWorks d ↔ A.CourierWorks d := by
  constructor
  · rintro ⟨s,b,ht⟩
    exact ⟨b,s,(transposeAllocation_trades A b s d).1 ht⟩
  · rintro ⟨b,s,ht⟩
    exact ⟨s,b,(transposeAllocation_trades A b s d).2 ht⟩

theorem transposeAllocation_delivers
    (A : Allocation B S D) (b : B) (s : S) :
    (transposeAllocation A).Delivers s b ↔ A.Delivers b s := by
  constructor
  · rintro ⟨d,ht⟩
    exact ⟨d,(transposeAllocation_trades A b s d).1 ht⟩
  · rintro ⟨d,ht⟩
    exact ⟨d,(transposeAllocation_trades A b s d).2 ht⟩

theorem courierSlot_transpose
    (A : Allocation B S D) (d : D) :
    courierSlot (transposeAllocation A) d =
      (courierSlot A d).map Prod.swap := by
  by_cases hw : A.CourierWorks d
  · obtain ⟨b,s,ht⟩ := hw
    have ht' : (transposeAllocation A).Trades s b d :=
      (transposeAllocation_trades A b s d).2 ht
    rw [courierSlot_eq_some_of_trade A ht]
    rw [courierSlot_eq_some_of_trade (transposeAllocation A) ht']
    rfl
  · have hw' : ¬ (transposeAllocation A).CourierWorks d := by
      intro h
      exact hw ((transposeAllocation_works A d).1 h)
    rw [(courierSlot_none_iff_idle A d).2 hw]
    rw [(courierSlot_none_iff_idle (transposeAllocation A) d).2 hw']
    rfl

theorem welfare_transpose (M : Market B S D) (A : Allocation B S D) :
    welfare (transposeMarket M) (transposeAllocation A) = welfare M A := by
  classical
  have h₁ := sum_assigned_eq_sum_courierSlots A
    (fun d b s => M.value b s - M.cost d b s)
  have h₂ := sum_assigned_eq_sum_courierSlots (transposeAllocation A)
    (fun d (s : S) (b : B) =>
      (transposeMarket M).value s b - (transposeMarket M).cost d s b)
  have h₁' : welfare M A = ∑ d : D, match courierSlot A d with
      | none => (0 : ℝ)
      | some (b,s) => M.value b s - M.cost d b s := by
    convert h₁ using 1 <;> rfl
  have h₂' : welfare (transposeMarket M) (transposeAllocation A) =
      ∑ d : D, match courierSlot (transposeAllocation A) d with
        | none => (0 : ℝ)
        | some (s,b) =>
            (transposeMarket M).value s b - (transposeMarket M).cost d s b := by
    convert h₂ using 1 <;> try rfl
    apply Finset.sum_congr rfl
    intro d _
    cases h : courierSlot (transposeAllocation A) d with
    | none => rfl
    | some sb => rcases sb with ⟨s,b⟩; rfl
  rw [h₁',h₂']
  apply Finset.sum_congr rfl
  intro d _
  rw [courierSlot_transpose A d]
  cases h : courierSlot A d with
  | none => rfl
  | some bs => rcases bs with ⟨b,s⟩; rfl

theorem optimal_transpose
    (M : Market B S D) (A : Allocation B S D)
    (hoptimal : IsWelfareOptimal M A) :
    IsWelfareOptimal (transposeMarket M) (transposeAllocation A) := by
  intro A'
  have h := hoptimal (transposeAllocation A')
  calc
    welfare (transposeMarket M) A' = welfare M (transposeAllocation A') := by
      simpa only [transposeMarket] using
        (welfare_transpose (transposeMarket M) A').symm
    _ ≤ welfare M A := h
    _ = welfare (transposeMarket M) (transposeAllocation A) :=
      (welfare_transpose M A).symm

theorem courierPlan_transpose_iff
    (M : Market B S D) (A : Allocation B S D) (w : B → S → ℝ) :
    IsCourierPlanFor M A w ↔
      IsCourierPlanFor (transposeMarket M) (transposeAllocation A)
        (fun s b => w b s) := by
  constructor
  · intro hp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s b
      exact hp.1 b s
    · intro d s b ht
      have ht' : A.Trades b s d := (transposeAllocation_trades A b s d).1 ht
      have h := hp.2.1 d b s ht'
      constructor
      · exact h.1
      · intro s' b'
        exact h.2 b' s'
    · intro d hd s b
      have hd' : ¬ A.CourierWorks d := by
        intro hw
        exact hd ((transposeAllocation_works A d).2 hw)
      exact hp.2.2.1 d hd' b s
    · intro s b hd
      have hd' : ¬ A.Delivers b s := by
        intro hw
        exact hd ((transposeAllocation_delivers A b s).2 hw)
      exact hp.2.2.2 b s hd'
  · intro hp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b s
      exact hp.1 s b
    · intro d b s ht
      have ht' : (transposeAllocation A).Trades s b d :=
        (transposeAllocation_trades A b s d).2 ht
      have h := hp.2.1 d s b ht'
      constructor
      · exact h.1
      · intro b' s'
        exact h.2 s' b'
    · intro d hd b s
      have hd' : ¬ (transposeAllocation A).CourierWorks d := by
        intro hw
        exact hd ((transposeAllocation_works A d).1 hw)
      exact hp.2.2.1 d hd' s b
    · intro b s hd
      have hd' : ¬ (transposeAllocation A).Delivers s b := by
        intro hw
        exact hd ((transposeAllocation_delivers A b s).1 hw)
      exact hp.2.2.2 s b hd'

private theorem realized_eq_trade_transpose_helper
    (M : Market B S D) (A : Allocation B S D) (w : B → S → ℝ)
    {b : B} {s : S} {d : D} (ht : A.Trades b s d) :
    courierRealizedUtility M A w d = w b s - M.cost d b s := by
  classical
  have hw : ∃ b' s', A.Trades b' s' d := ⟨b,s,ht⟩
  unfold courierRealizedUtility
  rw [dif_pos hw]
  let b₀ := Classical.choose hw
  let hs := Classical.choose_spec hw
  let s₀ := Classical.choose hs
  have ht₀ : A.Trades b₀ s₀ d := Classical.choose_spec hs
  have hb : b₀ = b := A.courier_unique ht₀ ht
  have ht₀' : A.Trades b s₀ d := by simpa [hb] using ht₀
  have hp : (s₀,d) = (s,d) := Option.some.inj (ht₀'.symm.trans ht)
  have hss : s₀ = s := congrArg Prod.fst hp
  change w b₀ s₀ - M.cost d b₀ s₀ = w b s - M.cost d b s
  rw [hb,hss]

theorem realizedUtility_transpose
    (M : Market B S D) (A : Allocation B S D)
    (w : B → S → ℝ) (d : D) :
    courierRealizedUtility (transposeMarket M) (transposeAllocation A)
      (fun s b => w b s) d = courierRealizedUtility M A w d := by
  classical
  by_cases hw : A.CourierWorks d
  · obtain ⟨b,s,ht⟩ := hw
    have ht' : (transposeAllocation A).Trades s b d :=
      (transposeAllocation_trades A b s d).2 ht
    rw [realized_eq_trade_transpose_helper (transposeMarket M)
      (transposeAllocation A) (fun s b => w b s) ht']
    rw [realized_eq_trade_transpose_helper M A w ht]
    rfl
  · have hw' : ¬ (transposeAllocation A).CourierWorks d := by
      intro h
      exact hw ((transposeAllocation_works A d).1 h)
    unfold courierRealizedUtility
    have hno' : ¬ ∃ s b, (transposeAllocation A).Trades s b d := hw'
    have hno : ¬ ∃ b s, A.Trades b s d := hw
    rw [dif_neg hno', dif_neg hno]

theorem maximalCourierUtility_transpose
    (M : Market B S D) (A : Allocation B S D) (uBar : D → ℝ)
    (hu : IsMaximalCourierUtility M A uBar) :
    IsMaximalCourierUtility (transposeMarket M) (transposeAllocation A) uBar := by
  obtain ⟨w,hplan,hreal⟩ := hu.1
  constructor
  · refine ⟨(fun s b => w b s), (courierPlan_transpose_iff M A w).1 hplan, ?_⟩
    intro d
    rw [realizedUtility_transpose M A w d]
    exact hreal d
  · intro w' hplan' d
    let w : B → S → ℝ := fun b s => w' s b
    have hplan : IsCourierPlanFor M A w :=
      (courierPlan_transpose_iff M A w).2 hplan'
    have hmax := hu.2 w hplan d
    change courierRealizedUtility (transposeMarket M) (transposeAllocation A)
      (fun s b => w b s) d ≤ uBar d
    rw [realizedUtility_transpose M A w d]
    exact hmax

theorem adjustedValue_transpose
    (M : Market B S D) (A : Allocation B S D)
    (uBar : D → ℝ) (b : B) (s : S) :
    adjustedValue (transposeMarket M) (transposeAllocation A) uBar s b =
      adjustedValue M A uBar b s := by
  unfold adjustedValue requiredTip
  by_cases hd : A.Delivers b s
  · have hd' : (transposeAllocation A).Delivers s b :=
      (transposeAllocation_delivers A b s).2 hd
    simp [hd, hd', transposeMarket]
  · have hd' : ¬ (transposeAllocation A).Delivers s b := by
      intro h
      exact hd ((transposeAllocation_delivers A b s).1 h)
    simp [hd, hd', transposeMarket]

noncomputable def transposeBuyerMatching (z : BuyerMatching B S) : BuyerMatching S B where
  assigned := fun s => if h : ∃ b, z.assigned b = some s then
    some (Classical.choose h) else none
  store_unique := by
    intro s₁ s₂ b h₁ h₂
    have h₁' : z.assigned b = some s₁ := by
      by_cases h : ∃ b, z.assigned b = some s₁
      · have hc := Classical.choose_spec h
        simp only [dif_pos h] at h₁
        have hb : Classical.choose h = b := Option.some.inj h₁
        simpa [hb] using hc
      · simp [h] at h₁
    have h₂' : z.assigned b = some s₂ := by
      by_cases h : ∃ b, z.assigned b = some s₂
      · have hc := Classical.choose_spec h
        simp only [dif_pos h] at h₂
        have hb : Classical.choose h = b := Option.some.inj h₂
        simpa [hb] using hc
      · simp [h] at h₂
    exact Option.some.inj (h₁'.symm.trans h₂')

theorem transposeBuyerMatching_iff
    (z : BuyerMatching B S) (b : B) (s : S) :
    (transposeBuyerMatching z).assigned s = some b ↔ z.assigned b = some s := by
  classical
  constructor
  · intro h
    have he : ∃ b, z.assigned b = some s := by
      by_contra hn
      simp [transposeBuyerMatching, hn] at h
    have hc := Classical.choose_spec he
    simp only [transposeBuyerMatching, dif_pos he] at h
    have hb : Classical.choose he = b := Option.some.inj h
    simpa [hb] using hc
  · intro hz
    have he : ∃ b, z.assigned b = some s := ⟨b,hz⟩
    have hc := Classical.choose_spec he
    have hb : Classical.choose he = b := z.store_unique hc hz
    simp [transposeBuyerMatching, he, hb]

theorem transposeBuyerMatching_weight
    (z : BuyerMatching B S) (q : B → S → ℝ) :
    matchingWeight (transposeBuyerMatching z) (fun s b => q b s) =
      matchingWeight z q := by
  classical
  have hPairs : buyerPairs (transposeBuyerMatching z) =
      (buyerPairs z).image Prod.swap := by
    ext p
    rcases p with ⟨s,b⟩
    constructor
    · intro hp
      have ht : (transposeBuyerMatching z).assigned s = some b := by
        simpa [buyerPairs] using hp
      have hz := (transposeBuyerMatching_iff z b s).1 ht
      exact Finset.mem_image.2 ⟨(b,s),by simp [buyerPairs,hz],rfl⟩
    · intro hp
      obtain ⟨p,hp,he⟩ := Finset.mem_image.1 hp
      have he' : p = (b,s) := by simpa using congrArg Prod.swap he
      rw [he'] at hp
      have hz : z.assigned b = some s := by simpa [buyerPairs] using hp
      simp [buyerPairs,(transposeBuyerMatching_iff z b s).2 hz]
  rw [← buyerPairs_weight (transposeBuyerMatching z) (fun s b => q b s)]
  rw [hPairs]
  have hsum : (∑ p ∈ (buyerPairs z).image Prod.swap, q p.2 p.1) =
      ∑ p ∈ buyerPairs z, q p.1 p.2 := by
    rw [Finset.sum_image]
    · simp
    · intro p hp r hr he
      have h := congrArg Prod.swap he
      simpa using h
  rw [hsum, buyerPairs_weight]

theorem transpose_original_matching_iff
    (A : Allocation B S D) (b : B) (s : S) :
    ((transposeAllocation A).toBuyerMatching).assigned s = some b ↔
      A.toBuyerMatching.assigned b = some s := by
  constructor
  · intro h
    change ((transposeAllocation A).assigned s).map Prod.fst = some b at h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨b₀,d⟩,ht,hb⟩ := h
    have hbb : b₀ = b := hb
    have ht' : A.Trades b s d :=
      (transposeAllocation_trades A b s d).1 (by
        change (transposeAllocation A).assigned s = some (b,d)
        simpa [hbb] using ht)
    change (A.assigned b).map Prod.fst = some s
    rw [ht']
    rfl
  · intro h
    change (A.assigned b).map Prod.fst = some s at h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₀,d⟩,ht,hs⟩ := h
    have hss : s₀ = s := hs
    have ht' : (transposeAllocation A).Trades s b d :=
      (transposeAllocation_trades A b s d).2 (by
        change A.assigned b = some (s,d)
        simpa [hss] using ht)
    change ((transposeAllocation A).assigned s).map Prod.fst = some b
    rw [ht']
    rfl

theorem original_matching_weight_transpose
    (M : Market B S D) (A : Allocation B S D) (uBar : D → ℝ) :
    matchingWeight ((transposeAllocation A).toBuyerMatching)
      (adjustedValue (transposeMarket M) (transposeAllocation A) uBar) =
    matchingWeight A.toBuyerMatching (adjustedValue M A uBar) := by
  classical
  let z := A.toBuyerMatching
  have hPairs : buyerPairs ((transposeAllocation A).toBuyerMatching) =
      buyerPairs (transposeBuyerMatching z) := by
    ext p
    rcases p with ⟨s,b⟩
    simp only [buyerPairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (transpose_original_matching_iff A b s).trans
      (transposeBuyerMatching_iff z b s).symm
  have hq : ∀ s b, adjustedValue (transposeMarket M)
      (transposeAllocation A) uBar s b = adjustedValue M A uBar b s :=
    fun s b => adjustedValue_transpose M A uBar b s
  rw [← buyerPairs_weight ((transposeAllocation A).toBuyerMatching)
    (adjustedValue (transposeMarket M) (transposeAllocation A) uBar)]
  rw [hPairs]
  have hsum : (∑ p ∈ buyerPairs (transposeBuyerMatching z),
      adjustedValue (transposeMarket M) (transposeAllocation A) uBar p.1 p.2) =
      ∑ p ∈ buyerPairs (transposeBuyerMatching z),
        adjustedValue M A uBar p.2 p.1 := by
    apply Finset.sum_congr rfl
    intro p _
    exact hq p.1 p.2
  rw [hsum]
  rw [buyerPairs_weight (transposeBuyerMatching z)
    (fun s b => adjustedValue M A uBar b s)]
  exact transposeBuyerMatching_weight z (adjustedValue M A uBar)

end PricingWithTips

/- Source: Scratch_PricingWithTips_buyer_global.lean -/

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]
  [Nonempty B] [Nonempty S] [Nonempty D]

theorem buyer_structured_adjusted_matching_global
    (M : Market B S D) (A : Allocation B S D)
    (cBS : B → S → ℝ) (cDB : D → B → ℝ)
    (hcost : ∀ d b s, M.cost d b s = cBS b s + cDB d b)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar) :
    IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by
  classical
  let MT := transposeMarket M
  let AT := transposeAllocation A
  have hcostT : ∀ d s b, MT.cost d s b = cBS b s + cDB d b := by
    intro d s b
    exact hcost d b s
  have hnotfullT : ¬ ∀ d, AT.CourierWorks d := by
    intro h
    apply hnotfull
    intro d
    exact (transposeAllocation_works A d).1 (h d)
  have hmaxT := store_structured_adjusted_matching_global MT AT
    (fun s b => cBS b s) cDB hcostT (optimal_transpose M A hoptimal)
    hnotfullT uBar (maximalCourierUtility_transpose M A uBar hu)
  intro z
  have h := hmaxT (transposeBuyerMatching z)
  change matchingWeight (transposeBuyerMatching z)
      (adjustedValue MT AT uBar) ≤
    matchingWeight AT.toBuyerMatching (adjustedValue MT AT uBar) at h
  have hz : matchingWeight (transposeBuyerMatching z)
      (adjustedValue MT AT uBar) =
      matchingWeight z (adjustedValue M A uBar) := by
    rw [show adjustedValue MT AT uBar =
        (fun s b => adjustedValue M A uBar b s) from by
          funext s b
          exact adjustedValue_transpose M A uBar b s]
    exact transposeBuyerMatching_weight z (adjustedValue M A uBar)
  rw [hz, original_matching_weight_transpose M A uBar] at h
  exact h

end PricingWithTips

open PricingWithTips

theorem solution {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
    [DecidableEq B] [DecidableEq S] [DecidableEq D]
    [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hcost : CourierBuyerDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (hnonempty : ∃ b, A.assigned b ≠ none)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar)
    (z : BuyerMatching B S)
    (hnew : ∃ b s, z.assigned b = some s ∧ A.assigned b = none) :
    matchingWeight z (adjustedValue M A uBar) ≤
      matchingWeight A.toBuyerMatching (adjustedValue M A uBar) := by
  obtain ⟨cBS,cDX,hdecomp⟩ := hcost
  exact PricingWithTips.buyer_structured_adjusted_matching_global
    M A cBS cDX hdecomp hoptimal hnotfull uBar hu z
