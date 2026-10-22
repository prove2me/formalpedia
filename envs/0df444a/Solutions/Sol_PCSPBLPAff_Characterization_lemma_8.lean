-- Prove2me | solution 1 for PCSPBLPAff.Characterization.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:42:37.491191+00:00
-- url     : https://prove2.me/submissions/8c1c5ccd-ed81-4db1-9af1-8c8860728f31

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

set_option autoImplicit false
open PCSPBLPAff.Characterization

theorem solution {τ : Type} {ar : τ → ℕ} {A B : Type}
    (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B)
    (h : HasMinionHomToPol 𝔸 𝔹) :
    ∀ L : ℕ, ∃ f : (Fin (2 * L + 1) → A) → B, PCSPBLPAff.Symmetric.IsPolymorphism 𝔸 𝔹 f ∧
      ∃ β : Fin (2 * L + 1) → Fin 2,
        (Finset.univ.filter (fun l => β l = 0)).card = L ∧
        (Finset.univ.filter (fun l => β l = 1)).card = L + 1 ∧
        PCSPBLPAff.Symmetric.IsBlockSymmetricFor β f := by
  obtain ⟨ξ, hξ⟩ := h
  intro L
  let β : Fin (2 * L + 1) → Fin 2 := fun l => if l.val < L then 0 else 1
  let w : Fin (2 * L + 1) → ℚ := fun _ => 1 / ((2 * L + 1 : ℕ) : ℚ)
  let r : Fin (2 * L + 1) → ℤ := fun l => if β l = 0 then -1 else 1
  have hcard0 : (Finset.univ.filter (fun l => β l = 0)).card = L := by
    have : Finset.univ.filter (fun l : Fin (2 * L + 1) => β l = 0)
        = Finset.univ.filter (fun l : Fin (2 * L + 1) => l.val < L) := by
      ext l
      simp [β]
    rw [this, Fin.card_filter_val_lt]
    omega
  have hcard1 : (Finset.univ.filter (fun l => β l = 1)).card = L + 1 := by
    have h1 : Finset.univ.filter (fun l : Fin (2 * L + 1) => β l = 1)
        = Finset.univ \ Finset.univ.filter (fun l : Fin (2 * L + 1) => β l = 0) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
      have : β l = 0 ∨ β l = 1 := by omega
      rcases this with h | h <;> simp [h]
    rw [h1, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
      Fintype.card_fin, hcard0]
    omega
  have hobj : IsBLPAffObj w r := by
    refine ⟨fun _ => ?_, ?_, ?_, ?_⟩
    · positivity
    · simp [w]
      field_simp
    · have hr : ∀ l : Fin (2 * L + 1), r l = if l.val < L then -1 else 1 := by
        intro l; simp [r, β]
      simp only [hr]
      rw [Fin.sum_univ_eq_sum_range (fun i => (if i < L then (-1 : ℤ) else 1)) (2 * L + 1)]
      rw [show 2 * L + 1 = L + (L + 1) by ring, Finset.sum_range_add]
      have e1 : ∑ x ∈ Finset.range L, (if x < L then (-1 : ℤ) else 1) = -(L : ℤ) := by
        rw [Finset.sum_congr rfl (g := fun _ => (-1 : ℤ))]
        · simp
        · intro x hx
          simp at hx
          simp [hx]
      have e2 : ∑ x ∈ Finset.range (L + 1), (if L + x < L then (-1 : ℤ) else 1) = (L : ℤ) + 1 := by
        rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ))]
        · simp
        · intro x hx
          simp
      rw [e1, e2]
      ring
    · intro i hi
      exfalso
      have hpos : (0 : ℚ) < 1 / ((2 * L + 1 : ℕ) : ℚ) := by positivity
      exact hpos.ne' hi
  refine ⟨ξ (2 * L + 1) ⟨(w, r), hobj⟩, (hξ (2 * L + 1) ⟨(w, r), hobj⟩).1, β, hcard0, hcard1, ?_⟩
  intro π hπ y
  have hq : minorQ (⇑π) w = w := by
    funext i
    have : Finset.univ.filter (fun j => π j = i) = {π.symm i} := by
      ext j
      simp [Equiv.apply_eq_iff_eq_symm_apply]
    simp [minorQ, this, w]
  have hz : minorZ (⇑π) r = r := by
    funext i
    have : Finset.univ.filter (fun j => π j = i) = {π.symm i} := by
      ext j
      simp [Equiv.apply_eq_iff_eq_symm_apply]
    simp only [minorZ, this, Finset.sum_singleton]
    have := hπ (π.symm i)
    simp only [Equiv.apply_symm_apply] at this
    simp [r, this]
  have hobj' : IsBLPAffObj (minorQ (⇑π) w) (minorZ (⇑π) r) := by rw [hq, hz]; exact hobj
  have key := (hξ (2 * L + 1) ⟨(w, r), hobj⟩).2 (2 * L + 1) (⇑π) hobj'
  have e : (⟨(minorQ (⇑π) w, minorZ (⇑π) r), hobj'⟩ : BLPAffObj (Fin (2 * L + 1)))
      = ⟨(w, r), hobj⟩ := Subtype.ext (Prod.ext hq hz)
  rw [e] at key
  have := congrFun key y
  simpa [polMinor] using this.symm
