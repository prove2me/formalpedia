-- Prove2me | solution 1 for OnlineCRS.Submod.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:41:55.012306+00:00
-- url     : https://prove2.me/submissions/6ef617d5-b3c2-4554-9b93-de522c553ce5

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_OnlineCRS_Submod_Model
import Definitions.Def_OnlineCRS_Submod_CRS

set_option autoImplicit false

namespace OnlineCRS.Submod

open OnlineCRS.Matroid

section Aux
variable {α : Type} [Fintype α] [DecidableEq α]

open Classical in
lemma charCRS_sum (w : (α → ℝ) → Finset (Finset α) → ℝ) (x : α → ℝ)
    (g : (Finset α → Finset α) → ℝ) :
    ∑ φ : Finset α → Finset α, charCRS w x φ * g φ = ∑ Fam : Finset (Finset α), w x Fam * g (charMap Fam) := by
  unfold charCRS
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Fam _
  have : ∀ φ : Finset α → Finset α,
      w x Fam * (if φ = charMap Fam then 1 else 0) * g φ = if φ = charMap Fam then w x Fam * g (charMap Fam) else 0 := by
    intro φ
    by_cases h : φ = charMap Fam
    · subst h; simp
    · simp [h]
  simp_rw [this]
  simp

/-- the product over the other elements -/
noncomputable def Rest (x : α → ℝ) (e : α) (A : Finset α) : ℝ :=
  ∏ f ∈ Finset.univ.erase e, if f ∈ A then x f else 1 - x f

lemma Rest_erase (x : α → ℝ) (e : α) (A : Finset α) : Rest x e (A.erase e) = Rest x e A := by
  unfold Rest
  apply Finset.prod_congr rfl
  intro f hf
  have : f ≠ e := (Finset.mem_erase.1 hf).1
  simp [Finset.mem_erase, this]

lemma activeProb_split (x : α → ℝ) (e : α) (A : Finset α) :
    activeProb x A = (if e ∈ A then x e else 1 - x e) * Rest x e A := by
  unfold activeProb Rest
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]

lemma selectable_erase (Fam : Finset (Finset α)) (A : Finset α) (e : α) :
    Selectable Fam A e ↔ Selectable Fam (A.erase e) e := by
  constructor
  · intro h I hI hIF
    exact h I (hI.trans (Finset.erase_subset _ _)) hIF
  · intro h I hI hIF
    by_cases heI : e ∈ I
    · rw [Finset.insert_eq_of_mem heI]; exact hIF
    · exact h I (by
        intro y hy
        exact Finset.mem_erase.2 ⟨by rintro rfl; exact heI hy, hI hy⟩) hIF

/-- toggling `e` -/
def toggle (e : α) (A : Finset α) : Finset α := if e ∈ A then A.erase e else insert e A

lemma toggle_invol (e : α) : Function.Involutive (toggle e) := by
  intro A
  by_cases h : e ∈ A
  · simp [toggle, h]
  · simp [toggle, h]

lemma sum_toggle (e : α) (K : Finset α → ℝ) (hK : ∀ A, K (A.erase e) = K A) :
    ∑ A : Finset α, (if e ∈ A then K A else 0) = ∑ A : Finset α, (if e ∈ A then 0 else K A) := by
  have := Equiv.sum_comp (Function.Involutive.toPerm (toggle e) (toggle_invol e))
    (fun A : Finset α => if e ∈ A then K A else 0)
  rw [← this]
  apply Finset.sum_congr rfl
  intro A _
  by_cases h : e ∈ A
  · simp [Function.Involutive.coe_toPerm, toggle, h]
  · have h2 : e ∈ insert e A := Finset.mem_insert_self _ _
    have : K (insert e A) = K A := by
      rw [← hK (insert e A), Finset.erase_insert h]
    simp [Function.Involutive.coe_toPerm, toggle, h, this]

open Classical in
lemma key_identity (x : α → ℝ) (Fam : Finset (Finset α)) (e : α) :
    ∑ A : Finset α, activeProb x A * (if e ∈ A ∧ Selectable Fam A e then 1 else 0)
      = x e * selProb x Fam e := by
  set K : Finset α → ℝ := fun A => if Selectable Fam A e then Rest x e A else 0 with hKdef
  have hK : ∀ A, K (A.erase e) = K A := by
    intro A
    simp only [hKdef, Rest_erase, ← selectable_erase]
  have h1 : ∀ A : Finset α, activeProb x A * (if e ∈ A ∧ Selectable Fam A e then 1 else 0)
      = x e * (if e ∈ A then K A else 0) := by
    intro A
    rw [activeProb_split x e A]
    by_cases h : e ∈ A <;> by_cases hs : Selectable Fam A e <;> simp [h, hs, hKdef]
  have h2 : ∀ A : Finset α, (if Selectable Fam A e then activeProb x A else 0)
      = (if e ∈ A then x e * K A else (1 - x e) * K A) := by
    intro A
    rw [activeProb_split x e A]
    by_cases h : e ∈ A <;> by_cases hs : Selectable Fam A e <;> simp [h, hs, hKdef]
  unfold selProb
  simp_rw [h1, h2]
  rw [← Finset.mul_sum]
  congr 1
  have h3 : ∀ A : Finset α, (if e ∈ A then x e * K A else (1 - x e) * K A)
      = x e * (if e ∈ A then K A else 0) + (1 - x e) * (if e ∈ A then 0 else K A) := by
    intro A; by_cases h : e ∈ A <;> simp [h]
  simp_rw [h3]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_toggle e K hK]
  ring

end Aux

end OnlineCRS.Submod

open OnlineCRS.Submod OnlineCRS.Matroid in
theorem solution {α : Type} [Fintype α] [DecidableEq α] (𝓕 : Finset α → Prop)
    (P : Set (α → ℝ)) (hPoly : IsPolytope P) (hRel : IsRelaxation 𝓕 P)
    (b c : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (w : (α → ℝ) → Finset (Finset α) → ℝ) (hw : OnlineCRS.Matroid.IsSelectableRand 𝓕 P b c w) :
    IsBalanced P b c (charCRS w) ∧ IsMonotoneCRS (charCRS w) := by
  classical
  obtain ⟨hrand, hsel⟩ := hw
  constructor
  · intro x hx e hxe
    have h1 : ∀ A : Finset α, ∑ φ : Finset α → Finset α, charCRS w x φ * (if e ∈ A ∧ e ∈ φ A then 1 else 0)
        = ∑ Fam : Finset (Finset α), w x Fam * (if e ∈ A ∧ Selectable Fam A e then 1 else 0) := by
      intro A
      rw [charCRS_sum w x (fun φ => if e ∈ A ∧ e ∈ φ A then 1 else 0)]
      apply Finset.sum_congr rfl
      intro Fam _
      congr 1
      unfold charMap
      by_cases h : e ∈ A ∧ Selectable Fam A e
      · simp [h, Finset.mem_filter]
      · have : ¬ (e ∈ A ∧ e ∈ A.filter (fun e => Selectable Fam A e)) := by
          simpa [Finset.mem_filter] using h
        simp [h, this]
    simp_rw [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ Fam : Finset (Finset α), ∑ A : Finset α, activeProb x A * (w x Fam * (if e ∈ A ∧ Selectable Fam A e then 1 else 0))
        = w x Fam * (x e * selProb x Fam e) := by
      intro Fam
      rw [← key_identity x Fam e, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _; ring
    simp_rw [h2]
    have := hsel x hx e
    have h3 : ∑ Fam : Finset (Finset α), w x Fam * (x e * selProb x Fam e)
        = x e * ∑ Fam : Finset (Finset α), w x Fam * selProb x Fam e := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Fam _; ring
    rw [h3]
    nlinarith
  · intro x e S₁ S₂ he hS
    unfold crsProb
    rw [charCRS_sum w x (fun φ => if e ∈ φ S₂ then 1 else 0),
      charCRS_sum w x (fun φ => if e ∈ φ S₁ then 1 else 0)]
    apply Finset.sum_le_sum
    intro Fam _
    obtain ⟨hw0, _, _⟩ := hrand x
    apply mul_le_mul_of_nonneg_left _ (hw0 Fam)
    by_cases h2 : e ∈ charMap Fam S₂
    · have h2' := Finset.mem_filter.1 h2
      have h1 : e ∈ charMap Fam S₁ := by
        unfold charMap
        rw [Finset.mem_filter]
        refine ⟨he, ?_⟩
        intro I hI hIF
        exact h2'.2 I (hI.trans hS) hIF
      simp [h1, h2]
    · simp only [h2, if_false]
      split_ifs <;> norm_num
