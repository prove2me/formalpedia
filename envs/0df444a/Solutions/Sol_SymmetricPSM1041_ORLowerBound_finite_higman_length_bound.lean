-- Prove2me | solution 1 for SymmetricPSM1041.ORLowerBound.finite_higman_length_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T14:27:46.489205+00:00
-- url     : https://prove2.me/submissions/f795898e-5d90-49d5-9c42-b37cce05a97c

import Mathlib

theorem solution (Alphabet : Type*) [Fintype Alphabet] :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ w : Fin m → List Alphabet,
      (∀ i, (w i).length = i.val + 1) →
      ∃ i j : Fin m, i < j ∧ (w i).Sublist (w j) := by
  classical
  by_contra! h
  let Bad (m : ℕ) :=
    {w : Fin m → List Alphabet //
      (∀ i, (w i).length = i.val + 1) ∧
      ∀ i j, i < j → ¬ (w i).Sublist (w j)}
  have bad_nonempty (m : ℕ) : Nonempty (Bad m) := by
    cases m with
    | zero =>
        exact ⟨⟨Fin.elim0, by simp⟩⟩
    | succ m =>
        obtain ⟨w, hw, hbad⟩ := h (m + 1) (by omega)
        exact ⟨⟨w, hw, by
          intro i j hij hs
          exact hbad i j hij hs⟩⟩
  have bad_finite (m : ℕ) : Finite (Bad m) := by
    letI (i : Fin m) : Finite {l : List Alphabet // l.length = i.val + 1} :=
      List.Vector.instFinite
    let e : Bad m → ((i : Fin m) → {l : List Alphabet // l.length = i.val + 1}) :=
      fun w i => ⟨w.1 i, w.2.1 i⟩
    have he : Function.Injective e := by
      intro u v huv
      apply Subtype.ext
      funext i
      exact congrArg Subtype.val (congrFun huv i)
    exact Finite.of_injective e he
  let proj {i j : ℕ} (hij : i ≤ j) (w : Bad j) : Bad i :=
    ⟨fun k => w.1 ⟨k.val, lt_of_lt_of_le k.isLt hij⟩,
      ⟨fun k => w.2.1 ⟨k.val, lt_of_lt_of_le k.isLt hij⟩,
        fun a b hab => w.2.2
          ⟨a.val, lt_of_lt_of_le a.isLt hij⟩
          ⟨b.val, lt_of_lt_of_le b.isLt hij⟩ hab⟩⟩
  have proj_refl (i : ℕ) (w : Bad i) : proj (le_refl i) w = w := by
    apply Subtype.ext
    funext k
    rfl
  have proj_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (w : Bad k) :
      proj hij (proj hjk w) = proj (hij.trans hjk) w := by
    apply Subtype.ext
    funext a
    rfl
  letI (m : ℕ) : Nonempty (Bad m) := bad_nonempty m
  letI (m : ℕ) : Finite (Bad m) := bad_finite m
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite
    (fun hij => proj hij) proj_refl
    (fun {i j k} hij hjk w => @proj_trans i j k hij hjk w)
    (fun _ _ => Set.toFinite _)
  let words : ℕ → List Alphabet := fun n => (f (n + 1)).1 ⟨n, by omega⟩
  have words_at (i j : ℕ) (hij : i ≤ j) :
      words i = (f (j + 1)).1 ⟨i, by omega⟩ := by
    have hp := hf (show i + 1 ≤ j + 1 by omega)
    have hp' := congrArg (fun w : Bad (i + 1) => w.1 ⟨i, by omega⟩) hp
    exact hp'.symm
  have hAlphabet : (Set.univ : Set Alphabet).PartiallyWellOrderedOn (· = ·) :=
    Set.toFinite Set.univ |>.partiallyWellOrderedOn
  have hLists := hAlphabet.partiallyWellOrderedOn_sublistForall₂
  obtain ⟨i, j, hij, hsub⟩ := hLists.exists_lt (f := words) (by simp [words])
  have hsub' : (words i).Sublist (words j) := by
    rw [List.sublistForall₂_iff] at hsub
    obtain ⟨l, heq, hl⟩ := hsub
    rw [List.forall₂_eq_eq_eq] at heq
    simpa [heq] using hl
  have hbad := (f (j + 1)).2.2
    ⟨i, by omega⟩ ⟨j, by omega⟩ (by simpa using hij)
  exact hbad (by simpa [words_at i j hij.le] using hsub')
