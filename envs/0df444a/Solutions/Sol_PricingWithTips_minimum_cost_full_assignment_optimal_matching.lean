-- Prove2me | solution 1 for PricingWithTips.minimum_cost_full_assignment_optimal_matching
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:20:19.454231+00:00
-- url     : https://prove2.me/submissions/f17f3b92-131a-4a31-9bef-8b3149d72c7e

import Theorems.Thm_PricingWithTips_sum_assigned_eq_sum_couriers
import Theorems.Thm_AssignmentGame_CoreCorners_worth_le_permutation_bound

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

private def Allocation.permuteCouriers (A : Allocation B S D) (σ : Equiv.Perm D) :
    Allocation B S D where
  assigned b := (A.assigned b).map (fun sd => (sd.1, σ sd.2))
  store_unique := by
    intro b₁ b₂ s d₁ d₂ h₁ h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨⟨s₁, k₁⟩, hk₁, hp₁⟩ := h₁
    obtain ⟨⟨s₂, k₂⟩, hk₂, hp₂⟩ := h₂
    have hs₁ : s₁ = s := congrArg Prod.fst hp₁
    have hs₂ : s₂ = s := congrArg Prod.fst hp₂
    subst s₁
    subst s₂
    exact A.store_unique hk₁ hk₂
  courier_unique := by
    intro b₁ b₂ s₁ s₂ d h₁ h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨⟨t₁, k₁⟩, hk₁, hp₁⟩ := h₁
    obtain ⟨⟨t₂, k₂⟩, hk₂, hp₂⟩ := h₂
    have ht₁ : t₁ = s₁ := congrArg Prod.fst hp₁
    have ht₂ : t₂ = s₂ := congrArg Prod.fst hp₂
    have hd₁ : σ k₁ = d := congrArg Prod.snd hp₁
    have hd₂ : σ k₂ = d := congrArg Prod.snd hp₂
    have hk : k₁ = k₂ := σ.injective (hd₁.trans hd₂.symm)
    subst t₁
    subst t₂
    subst k₂
    exact A.courier_unique hk₁ hk₂

private theorem Allocation.permuteCouriers_same_orders (A : Allocation B S D)
    (σ : Equiv.Perm D) (b : B) :
    ((A.permuteCouriers σ).assigned b).map Prod.fst =
      (A.assigned b).map Prod.fst := by
  cases h : A.assigned b with
  | none => simp [Allocation.permuteCouriers, h]
  | some sd => cases sd; simp [Allocation.permuteCouriers, h]

end PricingWithTips

open PricingWithTips AssignmentGame.CoreCorners

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ d, A.CourierWorks d)
    (hminimum : ∀ A' : Allocation B S D,
      (∀ b, (A'.assigned b).map Prod.fst = (A.assigned b).map Prod.fst) →
        welfare M A' ≤ welfare M A)
    (e : D ≃ {p : B × S // A.Delivers p.1 p.2})
    (he : ∀ d, A.Trades (e d).1.1 (e d).1.2 d)
    (C : ℝ) (hC : ∀ d b s, M.cost d b s < C) :
    (∑ d, (C - M.cost d (e d).1.1 (e d).1.2)) =
      (by
        classical
        exact AssignmentGame.CoreCorners.worth
          (fun d (o : {p : B × S // A.Delivers p.1 p.2}) =>
            C - M.cost d o.1.1 o.1.2) Finset.univ Finset.univ) := by
  classical
  let O := {p : B × S // A.Delivers p.1 p.2}
  let a : D → O → ℝ := fun d o => C - M.cost d o.1.1 o.1.2
  have ha : ∀ d o, 0 ≤ a d o := by
    intro d o
    dsimp [a]
    linarith [hC d o.1.1 o.1.2]
  let K : ℝ := ∑ d, a d (e d)
  have hperm : ∀ f : D ≃ O, (∑ d, a d (f d)) ≤ K := by
    intro f
    let σ : Equiv.Perm D := f.trans e.symm
    have hf : ∀ d, f d = e (σ d) := by
      intro d
      simp [σ]
    let A' : Allocation B S D := A.permuteCouriers σ.symm
    have horders : ∀ b, (A'.assigned b).map Prod.fst =
        (A.assigned b).map Prod.fst := by
      intro b
      exact A.permuteCouriers_same_orders σ.symm b
    have hwel := hminimum A' horders
    have hw0 : welfare M A =
        ∑ d, (M.value (e d).1.1 (e d).1.2 - M.cost d (e d).1.1 (e d).1.2) := by
      change (∑ b, match A.assigned b with
        | none => 0
        | some (s, d) => M.value b s - M.cost d b s) = _
      exact sum_assigned_eq_sum_couriers A e he
        (fun d b s => M.value b s - M.cost d b s)
    have hw1 : welfare M A' =
        ∑ d, (M.value (e d).1.1 (e d).1.2 -
          M.cost (σ.symm d) (e d).1.1 (e d).1.2) := by
      calc
        welfare M A' = ∑ b, match A.assigned b with
          | none => 0
          | some (s, d) => M.value b s - M.cost (σ.symm d) b s := by
            unfold welfare
            apply Finset.sum_congr rfl
            intro b _
            cases h : A.assigned b with
            | none => simp [A', Allocation.permuteCouriers, h]
            | some sd =>
              rcases sd with ⟨s, d⟩
              simp [A', Allocation.permuteCouriers, h]
        _ = _ := sum_assigned_eq_sum_couriers A e he
          (fun d b s => M.value b s - M.cost (σ.symm d) b s)
    rw [hw1, hw0] at hwel
    have hcost : (∑ d, M.cost d (e d).1.1 (e d).1.2) ≤
        ∑ d, M.cost (σ.symm d) (e d).1.1 (e d).1.2 := by
      simp only [Finset.sum_sub_distrib] at hwel
      linarith
    have hreindex :
        (∑ d, M.cost (σ.symm d) (e d).1.1 (e d).1.2) =
          ∑ d, M.cost d (e (σ d)).1.1 (e (σ d)).1.2 := by
      simpa using (Equiv.sum_comp σ.symm
        (fun d : D => M.cost d (e (σ d)).1.1 (e (σ d)).1.2))
    rw [hreindex] at hcost
    change (∑ d, (C - M.cost d (f d).1.1 (f d).1.2)) ≤
      ∑ d, (C - M.cost d (e d).1.1 (e d).1.2)
    simp_rw [hf]
    simp only [Finset.sum_sub_distrib]
    linarith
  have hupper : worth a Finset.univ Finset.univ ≤ K :=
    worth_le_permutation_bound a ha e K hperm
  let P : Finset (D × O) := Finset.univ.image (fun d => (d, e d))
  have hP : IsMatching Finset.univ Finset.univ P := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp
    · intro p hp q hq hfst
      obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨d', _, rfl⟩ := Finset.mem_image.mp hq
      simp only at hfst
      subst d'
      rfl
    · intro p hp q hq hsnd
      obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨d', _, rfl⟩ := Finset.mem_image.mp hq
      have hde : d = d' := e.injective hsnd
      subst d'
      rfl
  have hsum : (∑ p ∈ P, a p.1 p.2) = K := by
    dsimp [P, K]
    rw [Finset.sum_image]
    intro d _ d' _ hpair
    exact congrArg Prod.fst hpair
  have hmem : P ∈ matchings Finset.univ Finset.univ := by
    simp only [matchings, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hP.1, hP⟩
  have hlower : K ≤ worth a Finset.univ Finset.univ := by
    rw [← hsum]
    unfold worth
    exact Finset.le_sup' (fun P => ∑ p ∈ P, a p.1 p.2) hmem
  change K = worth a Finset.univ Finset.univ
  exact le_antisymm hlower hupper
