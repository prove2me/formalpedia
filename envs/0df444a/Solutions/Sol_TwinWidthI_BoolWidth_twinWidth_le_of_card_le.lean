-- Prove2me | solution 1 for TwinWidthI.BoolWidth.twinWidth_le_of_card_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:26:07.97371+00:00
-- url     : https://prove2.me/submissions/c62c1894-6946-43d7-b4fe-0be3ca75c623

import Mathlib
import Definitions.Def_TwinWidthI_BoolWidth_Setting
open TwinWidthI.BoolWidth
open Finset

theorem tw_merge_exists {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finpartition (univ : Finset V)) {X Y : Finset V} (hX : X ∈ P.parts) (hY : Y ∈ P.parts)
    (hXY : X ≠ Y) :
    ∃ Q : Finpartition (univ : Finset V),
      Q.parts = insert (X ∪ Y) ((P.parts.erase X).erase Y) := by
  classical
  set S : Finset (Finset V) := insert (X ∪ Y) ((P.parts.erase X).erase Y) with hS
  have hXne : X ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (P.nonempty_of_mem_parts hX)
  have hbot : (∅ : Finset V) ∉ S := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hXne (Finset.union_eq_empty.mp h.symm).1
    · have := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
      exact P.bot_notMem this
  have hdisj : ∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → Disjoint A B :=
    fun A hA B hB hAB => P.disjoint hA hB hAB
  have hind : S.SupIndep id := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro A hA B hB hAB
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hS] at hA hB
    simp only [Function.onFun, id]
    have memP : ∀ {Z}, Z ∈ (P.parts.erase X).erase Y → Z ∈ P.parts ∧ Z ≠ X ∧ Z ≠ Y := by
      intro Z hZ
      exact ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hZ),
        Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hZ), Finset.ne_of_mem_erase hZ⟩
    rcases hA with rfl | hA <;> rcases hB with rfl | hB
    · exact absurd rfl hAB
    · obtain ⟨hB1, hB2, hB3⟩ := memP hB
      exact Finset.disjoint_union_left.mpr
        ⟨hdisj _ hX _ hB1 (Ne.symm hB2), hdisj _ hY _ hB1 (Ne.symm hB3)⟩
    · obtain ⟨hA1, hA2, hA3⟩ := memP hA
      exact Finset.disjoint_union_right.mpr
        ⟨hdisj _ hA1 _ hX hA2, hdisj _ hA1 _ hY hA3⟩
    · exact hdisj _ (memP hA).1 _ (memP hB).1 hAB
  have hsup : S.sup id = univ := by
    apply Finset.eq_univ_of_forall
    intro v
    have hv : v ∈ (univ : Finset V) := Finset.mem_univ v
    rw [← P.sup_parts] at hv
    obtain ⟨Z, hZ, hvZ⟩ := Finset.mem_sup.mp hv
    rw [Finset.mem_sup]
    by_cases h1 : Z = X
    · exact ⟨X ∪ Y, Finset.mem_insert_self _ _, Finset.mem_union_left _ (h1 ▸ hvZ)⟩
    by_cases h2 : Z = Y
    · exact ⟨X ∪ Y, Finset.mem_insert_self _ _, Finset.mem_union_right _ (h2 ▸ hvZ)⟩
    exact ⟨Z, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, hZ⟩⟩),
      hvZ⟩
  refine ⟨Finpartition.ofErase S hind hsup, ?_⟩
  simp only [Finpartition.ofErase]
  exact Finset.erase_eq_of_notMem hbot

theorem tw_chain {V : Type*} [Fintype V] [DecidableEq V] :
    ∀ (k : ℕ) (P : Finpartition (univ : Finset V)), #P.parts = k →
      ∃ (M : ℕ) (Ps : Fin (M + 1) → Finpartition (univ : Finset V)),
        Ps 0 = P ∧ #(Ps (Fin.last M)).parts ≤ 1 ∧
        ∀ i : Fin M, IsMergeStep (Ps i.castSucc) (Ps i.succ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro P hk
    by_cases hle : #P.parts ≤ 1
    · exact ⟨0, fun _ => P, rfl, hle, fun i => Fin.elim0 i⟩
    · push_neg at hle
      obtain ⟨X, hX, Y, hY, hXY⟩ := Finset.one_lt_card.mp hle
      obtain ⟨Q, hQ⟩ := tw_merge_exists P hX hY hXY
      have hcard : #Q.parts < k := by
        rw [hQ, ← hk]
        have h1 := Finset.card_insert_le (X ∪ Y) ((P.parts.erase X).erase Y)
        have h2 : #((P.parts.erase X).erase Y) = #P.parts - 2 := by
          rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hXY, hY⟩),
            Finset.card_erase_of_mem hX]
          omega
        omega
      obtain ⟨M, Ps, h0, hlast, hstep⟩ := ih _ hcard Q rfl
      refine ⟨M + 1, Fin.cons P Ps, rfl, ?_, ?_⟩
      · rw [← Fin.succ_last, Fin.cons_succ]; exact hlast
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one]
          rw [show (1 : Fin (M + 2)) = (0 : Fin (M + 1)).succ from rfl, Fin.cons_succ, h0]
          exact ⟨X, hX, Y, hY, hXY, hQ⟩
        · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
          exact hstep j

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (N : ℕ) (hcard : Fintype.card V ≤ N) : TwinWidthLE G N := by
  obtain ⟨M, Ps, h0, hlast, hstep⟩ := tw_chain _ (⊥ : Finpartition (univ : Finset V)) rfl
  refine ⟨M, Ps, h0, hlast, hstep, fun i => ?_⟩
  intro X _
  classical
  calc _ ≤ #(Ps i).parts := Finset.card_filter_le _ _
    _ ≤ #(univ : Finset V) := (Ps i).card_parts_le_card
    _ = Fintype.card V := Finset.card_univ
    _ ≤ N := hcard
