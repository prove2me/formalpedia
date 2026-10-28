-- Prove2me | solution 1 for WHAdditivity.Renyi.trace_marginal_product
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:30:10.669227+00:00
-- url     : https://prove2.me/submissions/a500905c-09da-498f-92f5-23c3cb7de080

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

open WHAdditivity.Renyi Matrix
open scoped ComplexOrder

section helpers
open Classical

/-- site condition for `tensorIdentity Λ (reducedMatrix Λ ρ)` -/
def cnd {N : ℕ} (Λ : Finset (Fin N)) (j : Fin N) {α : Type} (a b u v : α) : Prop :=
  (j ∈ Λ → u = a ∧ v = b) ∧ (j ∉ Λ → a = b ∧ u = v)

lemma restrict_eq_iff {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) (z y : Config d) :
    restrict d Λ z = restrict d Λ y ↔ ∀ j ∈ Λ, z j = y j := by
  simp [restrict, funext_iff]

lemma restrict_eq_iff' {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) (z : Config d)
    (a : SubConfig d Λ) :
    restrict d Λ z = a ↔ ∀ j (h : j ∈ Λ), z j = a ⟨j, h⟩ := by
  simp [restrict, funext_iff]

lemma tI_apply {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) (ρ : Matrix (Config d) (Config d) ℂ)
    (y y' : Config d) :
    tensorIdentity d Λ (reducedMatrix d Λ ρ) y y' =
      ∑ z : Config d, ∑ z' : Config d,
        if (∀ j, cnd Λ j (y j) (y' j) (z j) (z' j)) then ρ z z' else 0 := by
  unfold tensorIdentity reducedMatrix
  simp only [Matrix.of_apply]
  split_ifs with h
  · apply Finset.sum_congr rfl; intro z _; apply Finset.sum_congr rfl; intro z' _
    have : (restrict d Λ z = restrict d Λ y ∧ restrict d Λ z' = restrict d Λ y' ∧
        ∀ j, j ∉ Λ → z j = z' j) ↔ ∀ j, cnd Λ j (y j) (y' j) (z j) (z' j) := by
      rw [restrict_eq_iff, restrict_eq_iff]
      constructor
      · rintro ⟨h1, h2, h3⟩ j
        exact ⟨fun hj => ⟨h1 j hj, h2 j hj⟩, fun hj => ⟨h j hj, h3 j hj⟩⟩
      · intro hc
        exact ⟨fun j hj => ((hc j).1 hj).1, fun j hj => ((hc j).1 hj).2,
          fun j hj => ((hc j).2 hj).2⟩
    by_cases hc : ∀ j, cnd Λ j (y j) (y' j) (z j) (z' j)
    · rw [if_pos (this.mpr hc), if_pos hc]
    · rw [if_neg (fun h' => hc (this.mp h')), if_neg hc]
  · symm; apply Finset.sum_eq_zero; intro z _; apply Finset.sum_eq_zero; intro z' _
    rw [if_neg]; intro hc; exact h fun j hj => ((hc j).2 hj).1

lemma count_pi {N : ℕ} (d : Fin N → ℕ) (g : (j : Fin N) → Fin (d j) → Fin (d j) → ℂ) :
    (∑ y : Config d, ∑ y' : Config d, ∏ j, g j (y j) (y' j)) =
      ∏ j, ∑ a : Fin (d j), ∑ b : Fin (d j), g j a b := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl; intro y _
  rw [Fintype.prod_sum]

lemma sum2_single {α β : Type} [Fintype α] [Fintype β] (f : α → β → ℂ) (u : α) (v : β)
    (hQ : ∀ a b, f a b ≠ 0 → a = u ∧ b = v) :
    (∑ a, ∑ b, f a b) = f u v := by
  rw [Finset.sum_eq_single u, Finset.sum_eq_single v]
  · intro b _ hb; by_contra h; exact hb (hQ _ _ h).2
  · simp
  · intro a _ ha; apply Finset.sum_eq_zero; intro b _; by_contra h; exact ha (hQ _ _ h).1
  · simp

lemma ite_ne_zero_imp {P : Prop} [Decidable P] (h : (if P then (1:ℂ) else 0) ≠ 0) : P := by
  by_contra hP; exact h (if_neg hP)

lemma site_count {N : ℕ} (Λ Λ' : Finset (Fin N)) (j : Fin N) (n : ℕ) (u v s t : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n,
      if (cnd Λ j a b u v ∧ cnd Λ' j b a s t) then (1:ℂ) else 0) =
    (if j ∈ (Λ ∪ Λ')ᶜ then (n:ℂ) else 1) *
      (if ((j ∈ Λ ∩ Λ' → s = v ∧ t = u) ∧ (j ∉ Λ ∩ Λ' → u = v ∧ s = t)) then 1 else 0) := by
  by_cases hj : j ∈ Λ <;> by_cases hj' : j ∈ Λ'
  · rw [sum2_single _ u v (by intro a b h; have h := ite_ne_zero_imp h; simp [cnd, hj, hj'] at h; exact ⟨h.1.1.symm, h.1.2.symm⟩)]
    simp [cnd, hj, hj']
  · rw [sum2_single _ u v (by intro a b h; have h := ite_ne_zero_imp h; simp [cnd, hj, hj'] at h; exact ⟨h.1.1.symm, h.1.2.symm⟩)]
    simp [cnd, hj, hj']
    by_cases h1 : u = v <;> by_cases h2 : s = t <;> simp [h1, h2, eq_comm]
  · rw [sum2_single _ t s (by intro a b h; have h := ite_ne_zero_imp h; simp [cnd, hj, hj'] at h; exact ⟨h.2.2.symm, h.2.1.symm⟩)]
    simp [cnd, hj, hj']
    by_cases h1 : u = v <;> by_cases h2 : s = t <;> simp [h1, h2, eq_comm]
  · have : ∀ a : Fin n, (∑ b : Fin n, if (cnd Λ j a b u v ∧ cnd Λ' j b a s t) then (1:ℂ) else 0)
        = if (u = v ∧ s = t) then 1 else 0 := by
      intro a
      rw [Finset.sum_eq_single a]
      · simp [cnd, hj, hj']
      · intro b _ hb; rw [if_neg]; intro h; simp [cnd, hj, hj'] at h; exact hb h.1.1.symm
      · simp
    rw [Finset.sum_congr rfl (fun a _ => this a)]
    simp [hj, hj']

lemma pull5 {α β γ δ ε : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    (f : α → β → γ → δ → ε → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) = ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, f a b c d e := by
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]

lemma pull6 {α β γ δ ε ζ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    [Fintype ζ] (f : α → β → γ → δ → ε → ζ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ g, f a b c d e g) = ∑ c, ∑ d, ∑ e, ∑ g, ∑ a, ∑ b, f a b c d e g := by
  rw [Finset.sum_congr rfl (fun a _ => pull5 (f a))]
  exact pull5 (fun a c d e g => ∑ b, f a b c d e g)

def hcnd {N : ℕ} (Λ Λ' : Finset (Fin N)) (j : Fin N) {α : Type} (u v s t : α) : Prop :=
  (j ∈ Λ ∩ Λ' → s = v ∧ t = u) ∧ (j ∉ Λ ∩ Λ' → u = v ∧ s = t)

lemma lhs_point {N : ℕ} (d : Fin N → ℕ) (ρ : Matrix (Config d) (Config d) ℂ)
    (Λ Λ' : Finset (Fin N)) (z z' w w' : Config d) :
    (∑ y : Config d, ∑ y' : Config d,
      (if (∀ j, cnd Λ j (y j) (y' j) (z j) (z' j)) then ρ z z' else 0) *
      (if (∀ j, cnd Λ' j (y' j) (y j) (w j) (w' j)) then ρ w w' else 0)) =
    ρ z z' * ρ w w' * ((∏ j ∈ (Λ ∪ Λ')ᶜ, (d j : ℂ)) *
      (if ∀ j, hcnd Λ Λ' j (z j) (z' j) (w j) (w' j) then 1 else 0)) := by
  have e1 : ∀ y y' : Config d,
      (if (∀ j, cnd Λ j (y j) (y' j) (z j) (z' j)) then ρ z z' else 0) *
      (if (∀ j, cnd Λ' j (y' j) (y j) (w j) (w' j)) then ρ w w' else 0) =
      ρ z z' * ρ w w' * ∏ j, (if (cnd Λ j (y j) (y' j) (z j) (z' j) ∧
          cnd Λ' j (y' j) (y j) (w j) (w' j)) then (1:ℂ) else 0) := by
    intro y y'
    by_cases h1 : ∀ j, cnd Λ j (y j) (y' j) (z j) (z' j) <;>
      by_cases h2 : ∀ j, cnd Λ' j (y' j) (y j) (w j) (w' j)
    · rw [if_pos h1, if_pos h2, Finset.prod_eq_one (fun j _ => if_pos ⟨h1 j, h2 j⟩)]; ring
    · push Not at h2; obtain ⟨j, hj⟩ := h2
      rw [if_pos h1, if_neg (by push Not; exact ⟨j, hj⟩),
        Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (fun h => hj h.2))]; ring
    · push Not at h1; obtain ⟨j, hj⟩ := h1
      rw [if_neg (by push Not; exact ⟨j, hj⟩),
        Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (fun h => hj h.1))]; ring
    · push Not at h1; obtain ⟨j, hj⟩ := h1
      rw [if_neg (by push Not; exact ⟨j, hj⟩),
        Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (fun h => hj h.1))]; ring
  simp_rw [e1, ← Finset.mul_sum]
  congr 1
  rw [count_pi d (fun j a b => if (cnd Λ j a b (z j) (z' j) ∧ cnd Λ' j b a (w j) (w' j)) then (1:ℂ) else 0)]
  rw [Finset.prod_congr rfl (fun j _ => site_count Λ Λ' j (d j) (z j) (z' j) (w j) (w' j))]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Fintype.prod_boole]
  congr 1
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; exact h2 h1) | (exfalso; exact h1 h2)

lemma rM_apply {N : ℕ} (d : Fin N → ℕ) (Λ : Finset (Fin N)) (ρ : Matrix (Config d) (Config d) ℂ)
    (a b : SubConfig d Λ) :
    reducedMatrix d Λ ρ a b = ∑ z : Config d, ∑ z' : Config d,
      if (restrict d Λ z = a ∧ restrict d Λ z' = b ∧ (∀ j, j ∉ Λ → z j = z' j)) then ρ z z' else 0 := by
  unfold reducedMatrix; simp only [Matrix.of_apply]

lemma rhs_point {N : ℕ} (d : Fin N → ℕ) (ρ : Matrix (Config d) (Config d) ℂ)
    (Λ Λ' : Finset (Fin N)) (z z' w w' : Config d) :
    (∑ a : SubConfig d (Λ ∩ Λ'), ∑ a' : SubConfig d (Λ ∩ Λ'),
      (if (restrict d (Λ ∩ Λ') z = a ∧ restrict d (Λ ∩ Λ') z' = a' ∧
          (∀ j, j ∉ Λ ∩ Λ' → z j = z' j)) then ρ z z' else 0) *
      (if (restrict d (Λ ∩ Λ') w = a' ∧ restrict d (Λ ∩ Λ') w' = a ∧
          (∀ j, j ∉ Λ ∩ Λ' → w j = w' j)) then ρ w w' else 0)) =
    ρ z z' * ρ w w' * (if ∀ j, hcnd Λ Λ' j (z j) (z' j) (w j) (w' j) then 1 else 0) := by
  rw [sum2_single _ (restrict d (Λ ∩ Λ') z) (restrict d (Λ ∩ Λ') z')]
  · have key : ((∀ j, j ∉ Λ ∩ Λ' → z j = z' j) ∧ restrict d (Λ ∩ Λ') w = restrict d (Λ ∩ Λ') z' ∧
        restrict d (Λ ∩ Λ') w' = restrict d (Λ ∩ Λ') z ∧ (∀ j, j ∉ Λ ∩ Λ' → w j = w' j)) ↔
        ∀ j, hcnd Λ Λ' j (z j) (z' j) (w j) (w' j) := by
      rw [restrict_eq_iff, restrict_eq_iff]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩ j
        exact ⟨fun hj => ⟨h2 j hj, h3 j hj⟩, fun hj => ⟨h1 j hj, h4 j hj⟩⟩
      · intro h
        exact ⟨fun j hj => ((h j).2 hj).1, fun j hj => ((h j).1 hj).1,
          fun j hj => ((h j).1 hj).2, fun j hj => ((h j).2 hj).2⟩
    by_cases hk : ∀ j, hcnd Λ Λ' j (z j) (z' j) (w j) (w' j)
    · obtain ⟨h1, h2, h3, h4⟩ := key.mpr hk
      rw [if_pos ⟨rfl, rfl, h1⟩, if_pos ⟨h2, h3, h4⟩, if_pos hk]; ring
    · rw [if_neg hk, mul_zero]
      by_cases h1 : ∀ j, j ∉ Λ ∩ Λ' → z j = z' j
      · rw [if_pos ⟨rfl, rfl, h1⟩, if_neg (fun h => hk (key.mp ⟨h1, h.1, h.2.1, h.2.2⟩)), mul_zero]
      · rw [if_neg (fun h => h1 h.2.2), zero_mul]
  · intro a b h
    by_contra hc
    apply h
    have : ¬ (restrict d (Λ ∩ Λ') z = a ∧ restrict d (Λ ∩ Λ') z' = b ∧
          (∀ j, j ∉ Λ ∩ Λ' → z j = z' j)) := fun h' => hc ⟨h'.1.symm, h'.2.1.symm⟩
    rw [if_neg this, zero_mul]


theorem solution (N : ℕ) (d : Fin N → ℕ) (ρ : Matrix (Config d) (Config d) ℂ)
    (Λ Λ' : Finset (Fin N)) :
    (tensorIdentity d Λ (reducedMatrix d Λ ρ) * tensorIdentity d Λ' (reducedMatrix d Λ' ρ)).trace =
      (∏ j ∈ (Λ ∪ Λ')ᶜ, (d j : ℂ)) * (reducedMatrix d (Λ ∩ Λ') ρ ^ 2).trace := by
  have hL : (tensorIdentity d Λ (reducedMatrix d Λ ρ) *
      tensorIdentity d Λ' (reducedMatrix d Λ' ρ)).trace =
      ∑ z : Config d, ∑ z' : Config d, ∑ w : Config d, ∑ w' : Config d,
        ρ z z' * ρ w w' * ((∏ j ∈ (Λ ∪ Λ')ᶜ, (d j : ℂ)) *
          (if ∀ j, hcnd Λ Λ' j (z j) (z' j) (w j) (w' j) then 1 else 0)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, tI_apply]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [pull6]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ =>
      Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
    rw [← lhs_point d ρ Λ Λ' z z' w w']
  have hR : (reducedMatrix d (Λ ∩ Λ') ρ ^ 2).trace =
      ∑ z : Config d, ∑ z' : Config d, ∑ w : Config d, ∑ w' : Config d,
        ρ z z' * ρ w w' * (if ∀ j, hcnd Λ Λ' j (z j) (z' j) (w j) (w' j) then 1 else 0) := by
    rw [pow_two]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, rM_apply]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [pull6]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ =>
      Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
    rw [← rhs_point d ρ Λ Λ' z z' w w']
  rw [hL, hR]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ =>
      Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => ?_
  ring

end helpers
