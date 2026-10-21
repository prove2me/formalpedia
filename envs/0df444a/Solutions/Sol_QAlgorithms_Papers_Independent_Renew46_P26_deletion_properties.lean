-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P26.deletion_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:30:07.851007+00:00
-- url     : https://prove2.me/submissions/ad2aa72e-73df-4b10-bf5c-453dcf3d6e09

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26
noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P26

attribute [local instance] Classical.propDecidable

theorem g64f_rn_mul {α : Type*} (g1 g2 : Equiv.Perm α) (e : Equiv.Perm (Option α)) :
    Equiv.removeNone (Equiv.optionCongr g1 * e * Equiv.optionCongr g2) =
      g1 * Equiv.removeNone e * g2 := by
  ext x
  simp only [Equiv.Perm.mul_apply]
  rcases h : e (some (g2 x)) with _ | y
  · have h1 : (Equiv.optionCongr g1 * e * Equiv.optionCongr g2) (some x) = none := by
      simp [Equiv.Perm.mul_apply, h]
    have h2 := Equiv.removeNone_none _ h1
    have h3 := Equiv.removeNone_none _ h
    rcases hz : e none with _ | z
    · exact absurd (h.trans hz.symm) (by intro hh; exact Option.some_ne_none _ (e.injective hh))
    rw [hz] at h3
    simp only [Equiv.Perm.mul_apply, Equiv.optionCongr_apply, Option.map_none, hz,
      Option.map_some] at h2
    rw [Option.some_inj] at h2 h3
    rw [h2, h3]
  · have h1 : (Equiv.optionCongr g1 * e * Equiv.optionCongr g2) (some x) = some (g1 y) := by
      simp [Equiv.Perm.mul_apply, h]
    have a := Equiv.removeNone_some _ ⟨_, h1⟩
    have b := Equiv.removeNone_some _ ⟨_, h⟩
    rw [h1] at a; rw [h] at b
    rw [Option.some_inj] at a b
    rw [a, b]

theorem g64f_pc_via (n : ℕ) (g : Equiv.Perm (Fin n)) :
    Equiv.permCongr finSuccEquivLast (g.viaEmbedding (prefixEmbedding (Nat.le_succ n))) =
      Equiv.optionCongr g := by
  ext x : 1
  rcases x with _ | i
  · simp [Equiv.permCongr_apply]
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem]
    · simp
    · rintro ⟨j, hj⟩
      have := congrArg Fin.val hj
      have h2 : ((prefixEmbedding (Nat.le_succ n)) j).val = j.val := rfl
      rw [h2, Fin.val_last] at this
      exact absurd this (by have := j.isLt; omega)
  · simp [Equiv.permCongr_apply]
    have hc : ∀ j : Fin n, Fin.castSucc j = prefixEmbedding (Nat.le_succ n) j := fun j => Fin.ext rfl
    rw [hc, Equiv.Perm.viaEmbedding_apply, ← hc]
    simp

theorem g64f_pc_mul {α β : Type*} (e : α ≃ β) (a b : Equiv.Perm α) :
    Equiv.permCongr e (a * b) = Equiv.permCongr e a * Equiv.permCongr e b := by
  ext x : 1
  simp [Equiv.permCongr_apply]

theorem solution (n : ℕ) :
    deleteLast n 1 = 1 ∧
    (∀ g : Equiv.Perm (Fin n),
      deleteLast n (g.viaEmbedding (prefixEmbedding (Nat.le_succ n))) = g) ∧
    (∀ g1 g2 : Equiv.Perm (Fin n), ∀ h : Equiv.Perm (Fin (n + 1)),
      deleteLast n ((g1.viaEmbedding (prefixEmbedding (Nat.le_succ n))) * h *
        (g2.viaEmbedding (prefixEmbedding (Nat.le_succ n)))) =
        g1 * deleteLast n h * g2) := by
  have h2 : ∀ g : Equiv.Perm (Fin n),
      deleteLast n (g.viaEmbedding (prefixEmbedding (Nat.le_succ n))) = g := by
    intro g
    rw [deleteLast, g64f_pc_via, Equiv.removeNone_optionCongr]
  refine ⟨?_, h2, ?_⟩
  · have := h2 1
    have e : (1 : Equiv.Perm (Fin n)).viaEmbedding (prefixEmbedding (Nat.le_succ n)) = 1 := by
      exact map_one (Equiv.Perm.viaEmbeddingHom (prefixEmbedding (Nat.le_succ n)))
    rwa [e] at this
  · intro g1 g2 h
    rw [deleteLast, g64f_pc_mul, g64f_pc_mul, g64f_pc_via, g64f_pc_via, g64f_rn_mul]
    rfl
