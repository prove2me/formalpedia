-- Prove2me | solution 1 for TwinWidthI.GridThm.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:27:45.595188+00:00
-- url     : https://prove2.me/submissions/b4dba2c8-61ab-4408-ab55-a460cdd32c02

import Mathlib
import Definitions.Def_TwinWidthI_GridThm_Setting

set_option autoImplicit false

namespace TwinWidthI.GridThm

theorem qqb_chain {n : ℕ} {β : Type*} (g : Fin n → β)
    (h : ∀ a b : Fin n, (b : ℕ) = a + 1 → g a = g b) : ∀ a b, g a = g b := by
  have key : ∀ d a (ha : a < n) (hb : a + d < n), g ⟨a, ha⟩ = g ⟨a + d, hb⟩ := by
    intro d
    induction d with
    | zero => intro a ha hb; rfl
    | succ d ih =>
      intro a ha hb
      rw [ih a ha (by omega)]
      exact h ⟨a + d, by omega⟩ ⟨a + (d + 1), hb⟩ (by simp; omega)
  have key2 : ∀ a b : Fin n, (a : ℕ) ≤ b → g a = g b := by
    intro a b hab
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab
    have := key d a a.2 (by have := b.2; omega)
    have e : b = ⟨a + d, by have := b.2; omega⟩ := Fin.ext (by simpa using hd)
    rw [e]; exact this
  intro a b
  rcases le_total (a : ℕ) b with hab | hab
  · exact key2 a b hab
  · exact (key2 b a hab).symm

end TwinWidthI.GridThm

open TwinWidthI.GridThm in
theorem solution {A : Type*} [Fintype A] {n m : ℕ} (M : Matrix (Fin n) (Fin m) A) :
    IsMixed M Finset.univ Finset.univ ↔ ∃ i j, IsCorner M i j := by
  constructor
  · intro hmix
    by_contra hno
    push_neg at hno
    -- every corner block is vertical or horizontal
    have hblk : ∀ (i i' : Fin n) (j j' : Fin m), (i' : ℕ) = i + 1 → (j' : ℕ) = j + 1 →
        IsVertical M {i, i'} {j, j'} ∨ IsHorizontal M {i, i'} {j, j'} := by
      intro i i' j j' hi hj
      have := hno i j
      unfold TwinWidthI.GridThm.IsCorner at this
      by_contra hc
      push_neg at hc
      exact this ⟨i', j', hi, hj, hc⟩
    obtain ⟨hnv, hnh⟩ := hmix
    -- step 1: some consecutive rows differ
    have step1 : ∃ r r' : Fin n, (r' : ℕ) = r + 1 ∧ ∃ j0, M r j0 ≠ M r' j0 := by
      by_contra hc
      push_neg at hc
      apply hnv
      intro i _ i' _ j _
      have := qqb_chain (fun r => M r j) (fun a b hab => hc a b hab j) i i'
      simpa using this
    obtain ⟨r, r', hrr, j0, hj0⟩ := step1
    -- step 2: rows r, r' differ everywhere
    have hD : ∀ j, M r j ≠ M r' j := by
      have := qqb_chain (fun j => (M r j ≠ M r' j)) (by
        intro a b hab
        rcases hblk r r' a b hrr hab with hv | hh
        · have h1 := hv r (by simp) r' (by simp) a (by simp)
          have h2 := hv r (by simp) r' (by simp) b (by simp)
          simp only [eq_iff_iff]
          constructor <;> intro h <;> exfalso <;> [exact h h1; exact h h2] 
        · have h1 := hh r (by simp) a (by simp) b (by simp)
          have h2 := hh r' (by simp) a (by simp) b (by simp)
          simp only [eq_iff_iff, h1, h2])
      intro j
      have := this j0 j
      rw [← this]; exact hj0
    -- row r is constant between consecutive columns
    have hK : ∀ i : Fin n, (∀ j j' : Fin m, (j' : ℕ) = j + 1 → M i j = M i j') → 
        ∀ i' : Fin n, (i' : ℕ) = i + 1 → ∀ j j' : Fin m, (j' : ℕ) = j + 1 → M i' j = M i' j' := by
      intro i hi i' hii' j j' hj
      rcases hblk i i' j j' hii' hj with hv | hh
      · have h1 := hv i (by simp) i' (by simp) j (by simp)
        have h2 := hv i (by simp) i' (by simp) j' (by simp)
        rw [← h1, ← h2]; exact hi j j' hj
      · exact hh i' (by simp) j (by simp) j' (by simp)
    have hK' : ∀ i : Fin n, ∀ i' : Fin n, (i' : ℕ) = i + 1 → 
        (∀ j j' : Fin m, (j' : ℕ) = j + 1 → M i' j = M i' j') → 
        ∀ j j' : Fin m, (j' : ℕ) = j + 1 → M i j = M i j' := by
      intro i i' hii' hi j j' hj
      rcases hblk i i' j j' hii' hj with hv | hh
      · have h1 := hv i (by simp) i' (by simp) j (by simp)
        have h2 := hv i (by simp) i' (by simp) j' (by simp)
        rw [h1, h2]; exact hi j j' hj
      · exact hh i (by simp) j (by simp) j' (by simp)
    have hKr : ∀ j j' : Fin m, (j' : ℕ) = j + 1 → M r j = M r j' := by
      intro j j' hj
      rcases hblk r r' j j' hrr hj with hv | hh
      · exfalso
        exact hD j (hv r (by simp) r' (by simp) j (by simp))
      · exact hh r (by simp) j (by simp) j' (by simp)
    have hall : ∀ i : Fin n, ∀ j j' : Fin m, (j' : ℕ) = j + 1 → M i j = M i j' := by
      have := qqb_chain (fun i : Fin n => (∀ j j' : Fin m, (j' : ℕ) = j + 1 → M i j = M i j')) (by
        intro a b hab
        apply propext
        exact ⟨fun h => hK a h b hab, fun h => hK' a b hab h⟩)
      intro i
      have h2 := this r i
      rw [← h2]; exact hKr
    apply hnh
    intro i _ j _ j' _
    have := qqb_chain (fun j => M i j) (fun a b hab => hall i a b hab) j j'
    simpa using this
  · rintro ⟨i, j, i', j', _, _, hm⟩
    obtain ⟨hv, hh⟩ := hm
    refine ⟨fun h => hv ?_, fun h => hh ?_⟩
    · intro a ha b hb c hc
      exact h a (Finset.mem_univ _) b (Finset.mem_univ _) c (Finset.mem_univ _)
    · intro a ha c hc d hd
      exact h a (Finset.mem_univ _) c (Finset.mem_univ _) d (Finset.mem_univ _)

