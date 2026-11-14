-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.finite_supermodular_telescoping_strict
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:24:20.540559+00:00
-- url     : https://prove2.me/submissions/569e82db-5f7d-434c-88fe-0f5bc1684396

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem solution {ι : Type} [DecidableEq ι] (v : Finset ι → ℝ)
    (hSM : ∀ S : Finset ι, ∀ i j, i ∉ S → j ∉ S → i ≠ j →
      v (insert i (insert j S)) + v S ≥ v (insert i S)+v (insert j S))
    (T : Finset ι) (i j : ι) (hi : i ∉ T) (hj : j ∉ T) (hij : i ≠ j)
    (hstrict : v {i,j} + v ∅ > v {i} + v {j}) :
    v (insert i (insert j T)) > v ∅ + ∑ a ∈ insert i (insert j T), (v {a} - v ∅) := by
  have hmarg (S : Finset ι) (a : ι) (ha : a ∉ S) :
      v (insert a S)-v S ≥ v {a}-v ∅ := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert b S hb ih =>
      have haS : a ∉ S := fun h => ha (Finset.mem_insert_of_mem h)
      have hab : a ≠ b := by intro h; subst a; exact ha (Finset.mem_insert_self _ _)
      have hind := ih haS
      have h := hSM S a b haS hb hab
      linarith
  have htel (T B : Finset ι) (hdis : Disjoint T B) :
      v (B ∪ T) ≥ v B + ∑ a ∈ T, (v {a} - v ∅) := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert a T ha ih =>
      have haB : a ∉ B := by
        intro h
        exact Finset.disjoint_left.mp hdis (Finset.mem_insert_self _ _) h
      have hdis' : Disjoint T B := by
        apply Finset.disjoint_left.mpr
        intro x hx hxB
        exact Finset.disjoint_left.mp hdis (Finset.mem_insert_of_mem hx) hxB
      have hnot : a ∉ B ∪ T := by simp [haB,ha]
      have hm := hmarg (B ∪ T) a hnot
      have hind := ih hdis'
      rw [Finset.sum_insert ha]
      have heq : B ∪ insert a T = insert a (B ∪ T) := by ext x; simp [or_assoc,or_comm,or_left_comm]
      rw [heq]
      linarith
  have hdis : Disjoint T ({i,j} : Finset ι) := by
    apply Finset.disjoint_left.mpr
    intro a ha hab
    simp only [Finset.mem_insert,Finset.mem_singleton] at hab
    rcases hab with rfl | rfl
    · exact hi ha
    · exact hj ha
  have hh := htel T {i,j} hdis
  have heq : ({i,j} : Finset ι) ∪ T = insert i (insert j T) := by ext a; simp [or_assoc]
  rw [heq] at hh
  have hjT : j ∉ T := hj
  have hiJT : i ∉ insert j T := by simp [hi,hij]
  rw [Finset.sum_insert hiJT, Finset.sum_insert hjT]
  linarith
