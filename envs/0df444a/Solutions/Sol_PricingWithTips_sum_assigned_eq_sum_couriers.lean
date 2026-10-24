-- Prove2me | solution 1 for PricingWithTips.sum_assigned_eq_sum_couriers
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:16:09.483457+00:00
-- url     : https://prove2.me/submissions/58ec7bde-d7a6-4977-b560-c8c037e29b41

import Definitions.Def_PricingWithTips_Model

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution
    (A : Allocation B S D)
    (e : D ≃ {p : B × S // A.Delivers p.1 p.2})
    (he : ∀ d, A.Trades (e d).1.1 (e d).1.2 d)
    (F : D → B → S → ℝ) :
    (∑ b, match A.assigned b with
      | none => 0
      | some (s, d) => F d b s) =
    ∑ d, F d (e d).1.1 (e d).1.2 := by
  classical
  let T : Finset B := Finset.univ.filter (fun b => (A.assigned b).isSome)
  let G : B → ℝ := fun b => match A.assigned b with
    | none => 0
    | some (s, d) => F d b s
  have hfilter : (∑ b, G b) = ∑ b ∈ T, G b := by
    simp only [T, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    cases h : A.assigned b with
    | none => simp [G, h]
    | some sd => simp [G, h]
  have hbij : (∑ d, F d (e d).1.1 (e d).1.2) = ∑ b ∈ T, G b := by
    apply Finset.sum_bij (fun d _ => (e d).1.1)
    · intro d _
      have ht : A.assigned (e d).1.1 = some ((e d).1.2, d) := he d
      simp [T, ht]
    · intro d₁ _ d₂ _ hb
      have h₁ := he d₁
      have h₂ := he d₂
      have h₁' : A.Trades (e d₂).1.1 (e d₁).1.2 d₁ := by simpa [hb] using h₁
      have hp : some ((e d₁).1.2, d₁) = some ((e d₂).1.2, d₂) := h₁'.symm.trans h₂
      exact congrArg Prod.snd (Option.some.inj hp)
    · intro b hb
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      cases h : A.assigned b with
      | none => simp [h] at hb
      | some sd =>
        rcases sd with ⟨s, d⟩
        refine ⟨d, Finset.mem_univ _, ?_⟩
        exact A.courier_unique (he d) h
    · intro d _
      dsimp [G]
      rw [show A.assigned (e d).1.1 = some ((e d).1.2, d) from he d]
  simpa only [G] using hfilter.trans hbij.symm
