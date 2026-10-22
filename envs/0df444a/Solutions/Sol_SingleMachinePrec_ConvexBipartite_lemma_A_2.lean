-- Prove2me | solution 1 for SingleMachinePrec.ConvexBipartite.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:35:26.080256+00:00
-- url     : https://prove2.me/submissions/6b27c59d-8583-48a5-ad21-809dd62690ea

import Mathlib
import Definitions.Def_SingleMachinePrec_ConvexBipartite_IncPartition

set_option autoImplicit false
open SingleMachinePrec.ConvexBipartite
open ConvexBipartiteOrder

theorem sm2_linext {α β : Type*} [LinearOrder β] (f : α → β) (hf : Function.Injective f) :
    IsLinearOrder α (fun x y => f x ≤ f y) :=
  { refl := fun x => le_refl _
    trans := fun x y z h1 h2 => le_trans h1 h2
    antisymm := fun x y h1 h2 => hf (le_antisymm h1 h2)
    total := fun x y => le_total _ _ }

def sm2_key1 {a b : ℕ} : Job a b → ℕ ×ₗ ℕ ×ₗ ℕ
  | Sum.inl i => toLex (0, toLex (a - (i : ℕ), 0))
  | Sum.inr k => toLex (1, toLex ((k : ℕ), 0))

theorem sm2_part1 {a b : ℕ} (C : ConvexBipartiteOrder a b) :
    ∃ L : Job a b → Job a b → Prop, IsLinearExtension (C.Ebar C.E1) L := by
  refine ⟨fun x y => sm2_key1 x ≤ sm2_key1 y, ⟨sm2_linext _ ?_, ?_⟩⟩
  · rintro (i | i) (j | j) h <;> simp [sm2_key1] at h
    · have := i.isLt; have := j.isLt
      congr 1; apply Fin.ext; omega
    · congr 1; exact Fin.ext h
  · intro x y hxy
    rcases hxy with hp | hE
    · rcases hp with rfl | ⟨i, k, rfl, rfl, -, -⟩
      · exact le_refl _
      · simp [sm2_key1, Prod.Lex.le_iff]
    · obtain ⟨-, hE⟩ := hE
      rcases x with i | i <;> rcases y with j | j <;>
        simp [ConvexBipartiteOrder.E1, sm2_key1, Prod.Lex.le_iff] at hE ⊢
      · have := i.isLt; have := j.isLt
        left; omega
      · omega

def sm2_key2 {a b : ℕ} (C : ConvexBipartiteOrder a b) : Job a b → ℕ ×ₗ ℕ ×ₗ ℕ
  | Sum.inl j => toLex ((j : ℕ), toLex (0, (j : ℕ)))
  | Sum.inr k => toLex ((C.r k : ℕ), toLex (1, (k : ℕ)))

theorem sm2_part2 {a b : ℕ} (C : ConvexBipartiteOrder a b) (hnum : Monotone C.l) :
    ∃ L : Job a b → Job a b → Prop, IsLinearExtension (C.Ebar C.E2) L := by
  refine ⟨fun x y => sm2_key2 C x ≤ sm2_key2 C y, ⟨sm2_linext _ ?_, ?_⟩⟩
  · rintro (i | i) (j | j) h <;> simp [sm2_key2] at h
    · congr 1; first | exact Fin.ext h | exact Fin.ext h.2
    · congr 1; first | exact Fin.ext h | exact Fin.ext h.2
  · intro x y hxy
    rcases hxy with hp | hE
    · rcases hp with rfl | ⟨i, k, rfl, rfl, -, h2⟩
      · exact le_refl _
      · simp [sm2_key2, Prod.Lex.le_iff]
        have : (i : ℕ) ≤ C.r k := h2
        omega
    · obtain ⟨hinc, hE⟩ := hE
      rcases x with i | i <;> rcases y with j | j
      · simp [ConvexBipartiteOrder.E2, sm2_key2, Prod.Lex.le_iff] at hE ⊢
        omega
      · simp [ConvexBipartiteOrder.E2] at hE
      · obtain ⟨k, hik, hk⟩ := (by simpa [ConvexBipartiteOrder.E2] using hE : ∃ k : Fin b, i < k ∧ C.prec (Sum.inl j) (Sum.inr k))
        have hnp := hinc.2
        simp [ConvexBipartiteOrder.prec] at hnp hk
        have h1 : C.l i ≤ C.l k := hnum hik.le
        have h2 : C.l i ≤ j := le_trans h1 hk.1
        have h3 : C.r i < j := hnp h2
        simp [sm2_key2, Prod.Lex.le_iff]
        first | exact h3 | (left; exact h3) | omega
      · simp [ConvexBipartiteOrder.E2] at hE

open Classical in
noncomputable def sm2_M {a b : ℕ} (C : ConvexBipartiteOrder a b) (j : Fin a) : ℕ :=
  (Finset.univ.filter (fun k : Fin b => C.prec (Sum.inl j) (Sum.inr k))).sup (fun k => (k : ℕ) + 1)

theorem sm2_M_ge {a b : ℕ} (C : ConvexBipartiteOrder a b) (j : Fin a) (k : Fin b)
    (h : C.prec (Sum.inl j) (Sum.inr k)) : (k : ℕ) + 1 ≤ sm2_M C j := by
  classical
  unfold sm2_M
  exact Finset.le_sup (f := fun k : Fin b => (k : ℕ) + 1) (Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩)

theorem sm2_M_le {a b : ℕ} (C : ConvexBipartiteOrder a b) (j : Fin a) (n : ℕ)
    (h : ∀ k : Fin b, C.prec (Sum.inl j) (Sum.inr k) → (k : ℕ) + 1 ≤ n) : sm2_M C j ≤ n := by
  classical
  unfold sm2_M
  refine Finset.sup_le fun k hk => h k (Finset.mem_filter.mp hk).2

noncomputable def sm2_key3 {a b : ℕ} (C : ConvexBipartiteOrder a b) : Job a b → ℕ ×ₗ ℕ ×ₗ ℕ
  | Sum.inl j => toLex (2 * (b - sm2_M C j) + 1, toLex ((j : ℕ), 0))
  | Sum.inr k => toLex (2 * (b - (k : ℕ)), toLex (0, 0))

theorem sm2_part3 {a b : ℕ} (C : ConvexBipartiteOrder a b) :
    ∃ L : Job a b → Job a b → Prop, IsLinearExtension (C.Ebar C.E3) L := by
  refine ⟨fun x y => sm2_key3 C x ≤ sm2_key3 C y, ⟨sm2_linext _ ?_, ?_⟩⟩
  · rintro (i | i) (j | j) h <;> simp [sm2_key3] at h
    · exact congrArg Sum.inl (Fin.ext h.2)
    · omega
    · omega
    · have := i.isLt; have := j.isLt
      exact congrArg Sum.inr (Fin.ext (by omega))
  · intro x y hxy
    rcases hxy with hp | hE
    · rcases hp with rfl | ⟨i, k, rfl, rfl, h1, h2⟩
      · exact le_refl _
      · have hk := sm2_M_ge C i k (Or.inr ⟨i, k, rfl, rfl, h1, h2⟩)
        have := k.isLt
        simp [sm2_key3, Prod.Lex.le_iff]
        left; omega
    · obtain ⟨hinc, hE⟩ := hE
      rcases x with i | i <;> rcases y with j | j
      · simp [ConvexBipartiteOrder.E3] at hE
      · simp [ConvexBipartiteOrder.E3] at hE
      · have hE' : ∀ k : Fin b, i < k → ¬ C.prec (Sum.inl j) (Sum.inr k) := by
          simpa [ConvexBipartiteOrder.E3] using hE
        have hnp := hinc.2
        have hM : sm2_M C j ≤ (i : ℕ) := by
          refine sm2_M_le C j i fun k hk => ?_
          rcases lt_trichotomy k i with h | h | h
          · exact h
          · exact absurd (h ▸ hk) hnp
          · exact absurd hk (hE' k h)
        have := i.isLt
        simp [sm2_key3, Prod.Lex.le_iff]
        left; omega
      · simp [ConvexBipartiteOrder.E3, sm2_key3, Prod.Lex.le_iff] at hE ⊢
        have := i.isLt; have := j.isLt
        omega

theorem solution {a b : ℕ} (C : ConvexBipartiteOrder a b) (hnum : Monotone C.l) :
    (∃ L : Job a b → Job a b → Prop, IsLinearExtension (C.Ebar C.E1) L) ∧
    (∃ L : Job a b → Job a b → Prop, IsLinearExtension (C.Ebar C.E2) L) ∧
    (∃ L : Job a b → Job a b → Prop, IsLinearExtension (C.Ebar C.E3) L) := by
  exact ⟨sm2_part1 C, sm2_part2 C hnum, sm2_part3 C⟩
