-- Prove2me | solution 1 for OverbookBL.claim_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:03:46.504397+00:00
-- url     : https://prove2.me/submissions/4da82c44-b0b3-4d69-bc87-58d1ab8d5f61

import Definitions.Def_OverbookBL_IsAdmissible

open OverbookBL in
theorem solution {k : ℕ} (I : OverbookBL.Instance k) (B : ℕ) (past Nf : Fin k → ℕ) : ∃ x : Fin k → ℕ, OverbookBL.IsGlobOpt I B past Nf x ∧ ∀ j, OverbookBL.IsLocOpt I B past Nf x j := by
  classical
  let S : Finset (Fin k → ℕ) := Fintype.piFinset (fun j => Finset.range (Nf j + 1))
  have memS : ∀ y, y ∈ S ↔ y ≤ Nf := by
    intro y
    simp only [S, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]
    exact Iff.rfl
  obtain ⟨x0, hx0S, hx0⟩ := S.exists_max_image (OverbookBL.obj I B past)
    ⟨0, (memS 0).2 (fun j => Nat.zero_le _)⟩
  let G := S.filter (fun y => OverbookBL.obj I B past y = OverbookBL.obj I B past x0)
  obtain ⟨x, hxG, hx⟩ := G.exists_max_image (fun y => ∑ j, y j)
    ⟨x0, Finset.mem_filter.2 ⟨hx0S, rfl⟩⟩
  rw [Finset.mem_filter] at hxG
  have hxN : x ≤ Nf := (memS x).1 hxG.1
  have glob : ∀ y, y ≤ Nf → OverbookBL.obj I B past y ≤ OverbookBL.obj I B past x :=
    fun y hy => (hx0 y ((memS y).2 hy)).trans hxG.2.ge
  have upd : ∀ j y, y ≤ Nf j → Function.update x j y ≤ Nf := by
    intro j y hy i
    by_cases h : i = j
    · subst h; rw [Function.update_self]; exact hy
    · rw [Function.update_of_ne h]; exact hxN i
  refine ⟨x, ⟨hxN, glob⟩, fun j => ⟨hxN, fun y hy => glob _ (upd j y hy), ?_⟩⟩
  intro y hxy hy
  rcases lt_or_eq_of_le (glob _ (upd j y hy)) with h | h
  · exact h
  · exfalso
    have hmem : Function.update x j y ∈ G :=
      Finset.mem_filter.2 ⟨(memS _).2 (upd j y hy), h.trans hxG.2⟩
    have h1 := hx _ hmem
    have h2 := Finset.sum_update_of_mem (Finset.mem_univ j) x y
    have h3 := Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ j) x
    omega
