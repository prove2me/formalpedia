-- Prove2me | solution 1 for PinwheelDensity.ExactRange.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:50:00.750805+00:00
-- url     : https://prove2.me/submissions/6c335cf3-c286-45be-a085-2135edbc74bd

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange.Dev.L22

theorem sum_ge (s : Finset ℕ) (h : ∀ x ∈ s, 1 ≤ x) : s.card * (s.card + 1) ≤ 2 * ∑ x ∈ s, x := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ x ∈ s, 1 ≤ x := fun x hx => h x (Finset.mem_insert_of_mem hx)
    have ha1 : 1 ≤ a := h a (Finset.mem_insert_self _ _)
    have hnot : a ∉ s := fun hh => lt_irrefl _ (ha a hh)
    have hsub : s ⊆ Finset.Ico 1 a := by
      intro x hx
      exact Finset.mem_Ico.mpr ⟨hs x hx, ha x hx⟩
    have hc := Finset.card_le_card hsub
    simp only [Nat.card_Ico] at hc
    rw [Finset.card_insert_of_notMem hnot, Finset.sum_insert hnot]
    have := ih hs
    have hc2 : s.card + 1 ≤ a := by omega
    nlinarith

end PinwheelDensity.ExactRange.Dev.L22

namespace PinwheelDensity.ExactRange

theorem chk_lemma_2_2 (A : List ℕ) (hA : ∀ a ∈ A, 1 ≤ a) (σ : ZSchedule A) (d : ℤ)
    (hd : σ.IsFreeDay d) : A.length * (A.length + 1) ≤ A.sum := by
  classical
  -- last execution before d
  have exL : ∀ i : Fin A.length, ∃ l : ℕ, 1 ≤ l ∧ d - l ∈ σ.days i := by
    intro i
    obtain ⟨x, hx1, hx2⟩ := σ.hits i (d - A.get i)
    obtain ⟨hx2a, hx2b⟩ := Set.mem_Ico.mp hx2
    have : x ≠ d := fun h => hd i (h ▸ hx1)
    have hp : 0 ≤ d - x := by omega
    refine ⟨(d - x).toNat, ?_, ?_⟩ <;> [omega; (convert hx1 using 1; omega)]
  have exR : ∀ i : Fin A.length, ∃ r : ℕ, 1 ≤ r ∧ d + r ∈ σ.days i := by
    intro i
    obtain ⟨x, hx1, hx2⟩ := σ.hits i (d + 1)
    obtain ⟨hx2a, hx2b⟩ := Set.mem_Ico.mp hx2
    refine ⟨(x - d).toNat, by omega, ?_⟩
    convert hx1 using 1; omega
  let ℓ : Fin A.length → ℕ := fun i => Nat.find (exL i)
  let r : Fin A.length → ℕ := fun i => Nat.find (exR i)
  have hℓ : ∀ i, 1 ≤ ℓ i ∧ d - (ℓ i : ℤ) ∈ σ.days i := fun i => Nat.find_spec (exL i)
  have hr : ∀ i, 1 ≤ r i ∧ d + (r i : ℤ) ∈ σ.days i := fun i => Nat.find_spec (exR i)
  have hℓm : ∀ i (l : ℕ), 1 ≤ l → d - (l : ℤ) ∈ σ.days i → ℓ i ≤ l :=
    fun i l h1 h2 => Nat.find_min' (exL i) ⟨h1, h2⟩
  have hrm : ∀ i (l : ℕ), 1 ≤ l → d + (l : ℤ) ∈ σ.days i → r i ≤ l :=
    fun i l h1 h2 => Nat.find_min' (exR i) ⟨h1, h2⟩
  have hsum : ∀ i, ℓ i + r i ≤ A.get i := by
    intro i
    obtain ⟨x, hx1, hx2⟩ := σ.hits i (d - ℓ i + 1)
    obtain ⟨hx2a, hx2b⟩ := Set.mem_Ico.mp hx2
    have hne : x ≠ d := fun h => hd i (h ▸ hx1)
    by_cases hlt : x < d
    · have := hℓm i (d - x).toNat (by omega) (by convert hx1 using 1; omega)
      omega
    · have := hrm i (x - d).toNat (by omega) (by convert hx1 using 1; omega)
      omega
  have hinjℓ : Function.Injective ℓ := by
    intro i j h
    by_contra hij
    have := σ.disjoint hij
    have h1 := (hℓ i).2
    have h2 := (hℓ j).2
    rw [h] at h1
    exact Set.disjoint_left.mp this h1 h2
  have hinjr : Function.Injective r := by
    intro i j h
    by_contra hij
    have := σ.disjoint hij
    have h1 := (hr i).2
    have h2 := (hr j).2
    rw [h] at h1
    exact Set.disjoint_left.mp this h1 h2
  have h1 := Dev.L22.sum_ge (Finset.univ.image ℓ) (by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (hℓ i).1)
  have h2 := Dev.L22.sum_ge (Finset.univ.image r) (by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (hr i).1)
  rw [Finset.card_image_of_injective _ hinjℓ, Finset.sum_image (fun a _ b _ h => hinjℓ h)] at h1
  rw [Finset.card_image_of_injective _ hinjr, Finset.sum_image (fun a _ b _ h => hinjr h)] at h2
  simp only [Finset.card_univ, Fintype.card_fin] at h1 h2
  have h3 : ∑ i : Fin A.length, (ℓ i + r i) ≤ ∑ i : Fin A.length, A.get i :=
    Finset.sum_le_sum fun i _ => hsum i
  rw [Finset.sum_add_distrib] at h3
  have h4 : ∑ i : Fin A.length, A.get i = A.sum := by
    rw [← List.sum_ofFn]; congr 1; exact (List.ofFn_get A)
  omega

end PinwheelDensity.ExactRange
end

theorem solution : type_of% @PinwheelDensity.ExactRange.chk_lemma_2_2 := @PinwheelDensity.ExactRange.chk_lemma_2_2
