-- Prove2me | solution 1 for OverbookBL.exists_admissible
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:53:37.328202+00:00
-- url     : https://prove2.me/submissions/0f092310-3e7b-4a1c-b74c-c1d1a4fd98e1

import Definitions.Def_OverbookBL_IsAdmissible

open OverbookBL in
theorem solution {k : ℕ} (I : Instance k) (B : ℕ) (past Nf : Fin k → ℕ) : ∃ x : Fin k → ℕ, IsAdmissible I B past Nf x := by
  classical
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      have := I.lam_sum
      simp at this
    · exact h
  let S := (Fintype.piFinset (fun j => Finset.range (Nf j + 1))).filter
    (fun x => ∃ e, IsIndexSol Nf x e)
  have hmemS : ∀ x, x ∈ S ↔ ∃ e, IsIndexSol Nf x e := by
    intro x
    simp only [S, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · rintro ⟨e, he⟩
      exact ⟨fun j => Nat.lt_succ_of_le (he.1 j), e, he⟩
  have hne : S.Nonempty := ⟨0, (hmemS 0).2 ⟨⟨0, hk⟩, fun j => Nat.zero_le _,
    fun j hj => absurd (show j.val < 0 from hj) (Nat.not_lt_zero _), fun j _ => rfl⟩⟩
  obtain ⟨x0, hx0S, hx0max⟩ := Finset.exists_max_image S (fun x => obj I B past x) hne
  let S' := S.filter (fun x => obj I B past x = obj I B past x0)
  have hne' : S'.Nonempty := ⟨x0, Finset.mem_filter.mpr ⟨hx0S, rfl⟩⟩
  obtain ⟨x, hxS', hxmax⟩ := Finset.exists_max_image S' (fun x => ∑ j, x j) hne'
  obtain ⟨hxS, hxobj⟩ := Finset.mem_filter.mp hxS'
  have hopt : ∀ y ∈ S, obj I B past y ≤ obj I B past x :=
    fun y hy => (hx0max y hy).trans hxobj.ge
  have htie : ∀ y ∈ S, obj I B past y = obj I B past x → ∑ j, y j ≤ ∑ j, x j :=
    fun y hy hyo => hxmax y (Finset.mem_filter.mpr ⟨hy, hyo.trans hxobj⟩)
  refine ⟨x, ⟨(hmemS x).1 hxS, fun y hy => hopt y ((hmemS y).2 hy)⟩, ?_⟩
  let E := Finset.univ.filter (fun e => IsIndexSol Nf x e)
  have hEne : E.Nonempty := by
    obtain ⟨e, he⟩ := (hmemS x).1 hxS
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
  have he0 : IsIndexSol Nf x (E.min' hEne) := (Finset.mem_filter.mp (E.min'_mem hEne)).2
  have hupd : ∀ yv, yv ≤ Nf (E.min' hEne) → Function.update x (E.min' hEne) yv ∈ S := by
    intro yv hyv
    apply (hmemS _).2
    refine ⟨E.min' hEne, ?_, ?_, ?_⟩
    · intro j
      by_cases h : j = E.min' hEne
      · rw [h, Function.update_self]; exact hyv
      · rw [Function.update_apply, if_neg h]; exact he0.1 j
    · intro j hj
      rw [Function.update_apply, if_neg (ne_of_lt hj)]
      exact he0.2.1 j hj
    · intro j hj
      rw [Function.update_apply, if_neg (ne_of_gt hj)]
      exact he0.2.2 j hj
  refine ⟨E.min' hEne, ⟨he0, fun e' he' hidx => ?_⟩, he0.1, ?_, ?_⟩
  · have := E.min'_le e' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hidx⟩)
    exact absurd he' (not_lt.mpr this)
  · intro yv hyv
    exact hopt _ (hupd yv hyv)
  · intro yv hlt hyv
    rcases lt_or_eq_of_le (hopt _ (hupd yv hyv)) with h | h
    · exact h
    · exfalso
      have h1 := htie _ (hupd yv hyv) h
      have h2 : ∑ j, x j < ∑ j, Function.update x (E.min' hEne) yv j := by
        apply Finset.sum_lt_sum
        · intro j _
          by_cases hj : j = E.min' hEne
          · rw [hj, Function.update_self]; exact hlt.le
          · rw [Function.update_apply, if_neg hj]
        · exact ⟨E.min' hEne, Finset.mem_univ _, by rw [Function.update_self]; exact hlt⟩
      omega
