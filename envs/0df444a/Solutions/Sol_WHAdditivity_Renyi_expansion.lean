-- Prove2me | solution 1 for WHAdditivity.Renyi.expansion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:33:10.013416+00:00
-- url     : https://prove2.me/submissions/2d962387-c559-4682-a0e2-1c8d2cd075a5

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



lemma wh_single (n : ℕ) (a b u v : Fin n) :
    wernerHolevo n (Matrix.single a b 1) u v =
      ((n : ℂ) - 1)⁻¹ * ((if (a = b ∧ u = v) then 1 else 0) - (if (u = b ∧ v = a) then 1 else 0)) := by
  unfold wernerHolevo
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.transpose_apply, Matrix.single_apply,
    smul_eq_mul, Matrix.one_apply]
  congr 1
  by_cases hab : a = b
  · subst hab; rw [Matrix.trace_single_eq_same]
    by_cases huv : u = v <;> simp [huv, eq_comm, and_comm]
  · rw [Matrix.trace_single_eq_of_ne _ _ _ hab]
    simp [hab, eq_comm, and_comm]

lemma prod_split {N : ℕ} (d : Fin N → ℕ) (y y' x x' : Config d) :
    (∏ j, wernerHolevo (d j) (Matrix.single (x j) (x' j) 1) (y j) (y' j)) =
      (∏ j, ((d j : ℂ) - 1)⁻¹) * ∑ t : Finset (Fin N), (-1 : ℂ) ^ t.card *
        (if ∀ j, cnd t j (y j) (y' j) (x' j) (x j) then 1 else 0) := by
  simp_rw [wh_single]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp_rw [sub_eq_neg_add]
  rw [Finset.prod_add, Finset.powerset_univ]
  apply Finset.sum_congr rfl; intro t _
  rw [Finset.prod_neg, mul_assoc]
  congr 1
  have : (∏ j ∈ t, (if (y j = x' j ∧ y' j = x j) then (1:ℂ) else 0)) *
      ∏ j ∈ Finset.univ \ t, (if (x j = x' j ∧ y j = y' j) then (1:ℂ) else 0) =
      ∏ j, (if cnd t j (y j) (y' j) (x' j) (x j) then (1:ℂ) else 0) := by
    rw [← Finset.prod_sdiff (Finset.subset_univ t) (f := fun j => if cnd t j (y j) (y' j) (x' j) (x j) then (1:ℂ) else 0), mul_comm]
    congr 1
    · apply Finset.prod_congr rfl; intro j hj
      have hj : j ∉ t := (Finset.mem_sdiff.mp hj).2
      by_cases h : x j = x' j ∧ y j = y' j
      · rw [if_pos h, if_pos]; exact ⟨fun hj' => absurd hj' hj, fun _ => ⟨h.2, h.1.symm⟩⟩
      · rw [if_neg h, if_neg]; intro hc; exact h ⟨((hc.2 hj).2).symm, (hc.2 hj).1⟩
    · apply Finset.prod_congr rfl; intro j hj
      by_cases h : y j = x' j ∧ y' j = x j
      · rw [if_pos h, if_pos]; exact ⟨fun _ => ⟨h.1.symm, h.2.symm⟩, fun hj' => absurd hj hj'⟩
      · rw [if_neg h, if_neg]; intro hc; exact h ⟨((hc.1 hj).1).symm, ((hc.1 hj).2).symm⟩
  rw [this]; convert Fintype.prod_boole (M₀ := ℂ)

theorem expansion_aux (N : ℕ) (d : Fin N → ℕ) (Ω : Config d → ℂ) :
    tensorChannel d (fun j => wernerHolevo (d j)) (pureState Ω) =
      (∏ j, ((d j : ℂ) - 1)⁻¹) • ∑ Λ : Finset (Fin N),
        ((-1 : ℂ) ^ Λ.card) • tensorIdentity d Λ (reducedMatrix d Λ (pureState (star Ω))) := by
  ext y y'
  simp only [tensorChannel, Matrix.of_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    tI_apply, prod_split]
  simp only [pureState, Matrix.vecMulVec_apply, Pi.star_apply, star_star]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

theorem solution (N : ℕ) (d : Fin N → ℕ) (hd : ∀ j, 2 ≤ d j) (Ω : Config d → ℂ)
    (hΩ : IsUnitVector Ω) :
    tensorChannel d (fun j => wernerHolevo (d j)) (pureState Ω) =
      (∏ j, ((d j : ℂ) - 1)⁻¹) • ∑ Λ : Finset (Fin N),
        ((-1 : ℂ) ^ Λ.card) • tensorIdentity d Λ (reducedMatrix d Λ (pureState (star Ω))) :=
  expansion_aux N d Ω

end helpers

