-- Prove2me | solution 1 for PricingWithTips.optimal_reassign_couriers_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T23:46:48.346362+00:00
-- url     : https://prove2.me/submissions/711768c6-6c54-4104-9692-0c3eebe9f464

import Definitions.Def_PricingWithTips_Model

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

private def reassignCouriers (A : Allocation B S D) (f : D ≃ D) :
    Allocation B S D where
  assigned := fun b => (A.assigned b).map (fun sd => (sd.1, f sd.2))
  store_unique := by
    intro b₁ b₂ s d₁ d₂ h₁ h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨⟨s₁,e₁⟩, ha₁, hm₁⟩ := h₁
    obtain ⟨⟨s₂,e₂⟩, ha₂, hm₂⟩ := h₂
    have hs₁ : s₁ = s := congrArg Prod.fst hm₁
    have hs₂ : s₂ = s := congrArg Prod.fst hm₂
    exact A.store_unique (by simpa [hs₁] using ha₁) (by simpa [hs₂] using ha₂)
  courier_unique := by
    intro b₁ b₂ s₁ s₂ d h₁ h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨⟨t₁,e₁⟩, ha₁, hm₁⟩ := h₁
    obtain ⟨⟨t₂,e₂⟩, ha₂, hm₂⟩ := h₂
    have hd₁ : f e₁ = d := congrArg Prod.snd hm₁
    have hd₂ : f e₂ = d := congrArg Prod.snd hm₂
    have he : e₁ = e₂ := f.injective (hd₁.trans hd₂.symm)
    subst e₂
    exact A.courier_unique ha₁ ha₂

theorem solution
    (M : Market B S D) (A : Allocation B S D)
    (hoptimal : IsWelfareOptimal M A) (f : D ≃ D) :
    (∑ b, match A.assigned b with
      | none => (0 : ℝ)
      | some (s,d) => M.cost d b s) ≤
    (∑ b, match A.assigned b with
      | none => (0 : ℝ)
      | some (s,d) => M.cost (f d) b s) := by
  classical
  let A' := reassignCouriers A f
  have hle := hoptimal A'
  let V : ℝ := ∑ b, match A.assigned b with
    | none => 0
    | some (s,_) => M.value b s
  let C : ℝ := ∑ b, match A.assigned b with
    | none => 0
    | some (s,d) => M.cost d b s
  let C' : ℝ := ∑ b, match A.assigned b with
    | none => 0
    | some (s,d) => M.cost (f d) b s
  have hwA : welfare M A = V - C := by
    unfold welfare
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    cases h : A.assigned b with
    | none => simp [V, C, h]
    | some sd => cases sd; simp [V, C, h]
  have hwA' : welfare M A' = V - C' := by
    unfold welfare
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    cases h : A.assigned b with
    | none => simp [A', reassignCouriers, V, C', h]
    | some sd => cases sd; simp [A', reassignCouriers, V, C', h]
  rw [hwA, hwA'] at hle
  linarith
