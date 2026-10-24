-- Prove2me | solution 1 for PricingWithTips.optimal_has_courier_plan
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:08:30.352038+00:00
-- url     : https://prove2.me/submissions/bfa1a843-0fb6-484d-9474-38240735a64e

import Definitions.Def_PricingWithTips_Model
import Theorems.Thm_PricingWithTips_optimal_reassign_couriers_cost_le
import Theorems.Thm_AssignmentGame_CoreCorners_core_nonempty
import Theorems.Thm_AssignmentGame_CoreCorners_core_dual_constraints
import Theorems.Thm_AssignmentGame_CoreCorners_worth_le_permutation_bound

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

theorem solution
    (M : Market B S D) (A : Allocation B S D)
    (hoptimal : IsWelfareOptimal M A) :
    ∃ w : B → S → ℝ, IsCourierPlanFor M A w := by
  classical
  obtain ⟨C,u,v,hu,hv,hdual,htight⟩ := optimalCourierSlot_dual M A hoptimal
  let w : B → S → ℝ := dualWage A C u
  have hnet_le : ∀ d b s, w b s - M.cost d b s ≤ v d := by
    intro d b s
    by_cases hd : A.Delivers b s
    · let d₀ := Classical.choose hd
      have ht₀ : A.Trades b s d₀ := Classical.choose_spec hd
      have hslot : courierSlot A d₀ = some (b,s) :=
        courierSlot_eq_some_of_trade A ht₀
      have hdual' := hdual d₀ d
      simp only [courierWeight, hslot] at hdual'
      have hw : w b s = C - u d₀ := dualWage_eq_of_trade A C u ht₀
      rw [hw]
      linarith
    · have hw : w b s = 0 := dualWage_zero_off A C u b s hd
      rw [hw]
      linarith [M.cost_nonneg d b s, hv d]
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro b s
    by_cases hd : A.Delivers b s
    · obtain ⟨d,ht⟩ := hd
      have hslot : courierSlot A d = some (b,s) :=
        courierSlot_eq_some_of_trade A ht
      have htight' := htight d
      simp only [courierWeight, hslot] at htight'
      have hw : w b s = C - u d := dualWage_eq_of_trade A C u ht
      rw [hw]
      linarith [M.cost_nonneg d b s, hv d]
    · have hw : w b s = 0 := dualWage_zero_off A C u b s hd
      rw [hw]
  · intro d b s ht
    have hslot : courierSlot A d = some (b,s) :=
      courierSlot_eq_some_of_trade A ht
    have htight' := htight d
    simp only [courierWeight, hslot] at htight'
    have hw : w b s = C - u d := dualWage_eq_of_trade A C u ht
    constructor
    · rw [hw]
      linarith [hv d]
    · intro b' s'
      have hle := hnet_le d b' s'
      rw [hw]
      linarith
  · intro d hd b s
    have hslot : courierSlot A d = none :=
      (courierSlot_none_iff_idle A d).2 hd
    have htight' := htight d
    simp only [courierWeight, hslot] at htight'
    have hvzero : v d = 0 := by linarith [hu d, hv d]
    have hle := hnet_le d b s
    linarith
  · intro b s hd
    exact dualWage_zero_off A C u b s hd
