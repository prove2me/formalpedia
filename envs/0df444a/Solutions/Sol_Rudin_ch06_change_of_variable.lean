-- Prove2me | solution 1 for Rudin.ch06_change_of_variable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T00:30:19.873323+00:00
-- url     : https://prove2.me/submissions/00ad62b5-9570-4657-945e-3a652f2836eb

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace R619

open Rudin

theorem pmono {a b : ℝ} (P : Partition a b) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ P.n → P.x i ≤ P.x j := by
  intro i j
  induction j with
  | zero =>
    intro hij _
    have : i = 0 := Nat.le_zero.1 hij
    subst this; exact le_rfl
  | succ k ih =>
    intro hij hj
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · exact le_trans (ih (by omega) (by omega)) (P.mono k (by omega))
    · have hik : i = k + 1 := by omega
      subst hik; exact le_rfl

theorem pmem {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i ≤ P.n) : P.x i ∈ Set.Icc a b := by
  refine ⟨?_, ?_⟩
  · have h := pmono P (Nat.zero_le i) hi
    rwa [P.first] at h
  · have h := pmono P hi (le_refl P.n)
    rwa [P.last] at h

/-- A continuous strictly increasing map carries a subinterval onto the corresponding
subinterval. -/
theorem image_Icc {A B : ℝ} {φ : ℝ → ℝ} (hmono : StrictMonoOn φ (Set.Icc A B))
    (hc : ContinuousOn φ (Set.Icc A B)) {u v : ℝ} (hu : u ∈ Set.Icc A B) (hv : v ∈ Set.Icc A B)
    (huv : u ≤ v) : φ '' Set.Icc u v = Set.Icc (φ u) (φ v) := by
  have hsub : Set.Icc u v ⊆ Set.Icc A B := Set.Icc_subset_Icc hu.1 hv.2
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨t, ht, rfl⟩
    exact ⟨hmono.monotoneOn hu (hsub ht) ht.1, hmono.monotoneOn (hsub ht) hv ht.2⟩
  · exact intermediate_value_Icc huv (hc.mono hsub)


variable {a b A B : ℝ} {f α φ : ℝ → ℝ}

/-- The upper sum depends only on the division points up to the index `n`. -/
theorem upperSum_congr {P P' : Partition a b} (hn : P.n = P'.n)
    (hx : ∀ i ≤ P.n, P.x i = P'.x i) : upperSum f α P = upperSum f α P' := by
  unfold upperSum
  rw [hn]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [hx i (by omega), hx (i + 1) (by omega)]

theorem lowerSum_congr {P P' : Partition a b} (hn : P.n = P'.n)
    (hx : ∀ i ≤ P.n, P.x i = P'.x i) : lowerSum f α P = lowerSum f α P' := by
  unfold lowerSum
  rw [hn]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [hx i (by omega), hx (i + 1) (by omega)]

/-- Pushing a partition of `[A,B]` forward along `φ`. -/
def push (hφmono : StrictMonoOn φ (Set.Icc A B)) (hφA : φ A = a) (hφB : φ B = b)
    (Q : Partition A B) : Partition a b where
  n := Q.n
  x := fun i => φ (Q.x i)
  first := by rw [Q.first, hφA]
  last := by rw [Q.last, hφB]
  mono := fun i hi =>
    hφmono.monotoneOn (pmem Q (by omega)) (pmem Q (by omega)) (Q.mono i hi)

theorem upperSum_push (hφmono : StrictMonoOn φ (Set.Icc A B))
    (hφc : ContinuousOn φ (Set.Icc A B)) (hφA : φ A = a) (hφB : φ B = b) (Q : Partition A B) :
    upperSum (f ∘ φ) (α ∘ φ) Q = upperSum f α (push hφmono hφA hφB Q) := by
  unfold upperSum
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hi' : i < Q.n := hi
  show sSup ((f ∘ φ) '' Set.Icc (Q.x i) (Q.x (i + 1))) * (α (φ (Q.x (i + 1))) - α (φ (Q.x i)))
      = sSup (f '' Set.Icc (φ (Q.x i)) (φ (Q.x (i + 1)))) * (α (φ (Q.x (i + 1))) - α (φ (Q.x i)))
  rw [Set.image_comp,
    image_Icc hφmono hφc (pmem Q (le_of_lt hi')) (pmem Q hi') (Q.mono i hi')]

theorem lowerSum_push (hφmono : StrictMonoOn φ (Set.Icc A B))
    (hφc : ContinuousOn φ (Set.Icc A B)) (hφA : φ A = a) (hφB : φ B = b) (Q : Partition A B) :
    lowerSum (f ∘ φ) (α ∘ φ) Q = lowerSum f α (push hφmono hφA hφB Q) := by
  unfold lowerSum
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hi' : i < Q.n := hi
  show sInf ((f ∘ φ) '' Set.Icc (Q.x i) (Q.x (i + 1))) * (α (φ (Q.x (i + 1))) - α (φ (Q.x i)))
      = sInf (f '' Set.Icc (φ (Q.x i)) (φ (Q.x (i + 1)))) * (α (φ (Q.x (i + 1))) - α (φ (Q.x i)))
  rw [Set.image_comp,
    image_Icc hφmono hφc (pmem Q (le_of_lt hi')) (pmem Q hi') (Q.mono i hi')]


/-- `φ` maps `[A,B]` onto `[a,b]`. -/
theorem surj (hφmono : StrictMonoOn φ (Set.Icc A B)) (hφc : ContinuousOn φ (Set.Icc A B))
    (hAB : A ≤ B) (hφA : φ A = a) (hφB : φ B = b) :
    ∀ x ∈ Set.Icc a b, ∃ y ∈ Set.Icc A B, φ y = x := by
  intro x hx
  have himg := image_Icc hφmono hφc (Set.left_mem_Icc.2 hAB) (Set.right_mem_Icc.2 hAB) hAB
  rw [hφA, hφB] at himg
  have : x ∈ φ '' Set.Icc A B := by rw [himg]; exact hx
  obtain ⟨y, hy, hyx⟩ := this
  exact ⟨y, hy, hyx⟩

/-- Pulling a partition of `[a,b]` back along `φ`. -/
noncomputable def pull (hφmono : StrictMonoOn φ (Set.Icc A B))
    (hφc : ContinuousOn φ (Set.Icc A B)) (hAB : A ≤ B) (hφA : φ A = a) (hφB : φ B = b)
    (P : Partition a b) : Partition A B where
  n := P.n
  x := fun i => if h : i ≤ P.n then (surj hφmono hφc hAB hφA hφB _ (pmem P h)).choose else A
  first := by
    rw [dif_pos (Nat.zero_le _)]
    set y := (surj hφmono hφc hAB hφA hφB _ (pmem P (Nat.zero_le _))).choose with hy
    have hspec := (surj hφmono hφc hAB hφA hφB _ (pmem P (Nat.zero_le _))).choose_spec
    refine hφmono.injOn hspec.1 (Set.left_mem_Icc.2 hAB) ?_
    rw [hspec.2, P.first, hφA]
  last := by
    rw [dif_pos (le_refl _)]
    have hspec := (surj hφmono hφc hAB hφA hφB _ (pmem P (le_refl P.n))).choose_spec
    refine hφmono.injOn hspec.1 (Set.right_mem_Icc.2 hAB) ?_
    rw [hspec.2, P.last, hφB]
  mono := by
    intro i hi
    rw [dif_pos (le_of_lt hi), dif_pos (show i + 1 ≤ P.n from hi)]
    have h1 := (surj hφmono hφc hAB hφA hφB _ (pmem P (le_of_lt hi))).choose_spec
    have h2 := (surj hφmono hφc hAB hφA hφB _ (pmem P (show i + 1 ≤ P.n from hi))).choose_spec
    refine (hφmono.le_iff_le h1.1 h2.1).1 ?_
    rw [h1.2, h2.2]
    exact P.mono i hi

theorem push_pull_x (hφmono : StrictMonoOn φ (Set.Icc A B))
    (hφc : ContinuousOn φ (Set.Icc A B)) (hAB : A ≤ B) (hφA : φ A = a) (hφB : φ B = b)
    (P : Partition a b) (i : ℕ) (hi : i ≤ P.n) :
    (push hφmono hφA hφB (pull hφmono hφc hAB hφA hφB P)).x i = P.x i := by
  show φ ((pull hφmono hφc hAB hφA hφB P).x i) = P.x i
  show φ (if h : i ≤ P.n then (surj hφmono hφc hAB hφA hφB _ (pmem P h)).choose else A) = P.x i
  rw [dif_pos hi]
  exact (surj hφmono hφc hAB hφA hφB _ (pmem P hi)).choose_spec.2


/-- The two families of upper sums coincide. -/
theorem upper_sets_eq (hφmono : StrictMonoOn φ (Set.Icc A B))
    (hφc : ContinuousOn φ (Set.Icc A B)) (hAB : A ≤ B) (hφA : φ A = a) (hφB : φ B = b) :
    {y : ℝ | ∃ Q : Partition A B, y = upperSum (f ∘ φ) (α ∘ φ) Q}
      = {y : ℝ | ∃ P : Partition a b, y = upperSum f α P} := by
  ext y
  constructor
  · rintro ⟨Q, rfl⟩
    exact ⟨push hφmono hφA hφB Q, upperSum_push hφmono hφc hφA hφB Q⟩
  · rintro ⟨P, rfl⟩
    refine ⟨pull hφmono hφc hAB hφA hφB P, ?_⟩
    rw [upperSum_push hφmono hφc hφA hφB]
    exact upperSum_congr (f := f) (α := α) (P := P)
      (P' := push hφmono hφA hφB (pull hφmono hφc hAB hφA hφB P)) rfl
      (fun i hi => (push_pull_x hφmono hφc hAB hφA hφB P i hi).symm)

theorem lower_sets_eq (hφmono : StrictMonoOn φ (Set.Icc A B))
    (hφc : ContinuousOn φ (Set.Icc A B)) (hAB : A ≤ B) (hφA : φ A = a) (hφB : φ B = b) :
    {y : ℝ | ∃ Q : Partition A B, y = lowerSum (f ∘ φ) (α ∘ φ) Q}
      = {y : ℝ | ∃ P : Partition a b, y = lowerSum f α P} := by
  ext y
  constructor
  · rintro ⟨Q, rfl⟩
    exact ⟨push hφmono hφA hφB Q, lowerSum_push hφmono hφc hφA hφB Q⟩
  · rintro ⟨P, rfl⟩
    refine ⟨pull hφmono hφc hAB hφA hφB P, ?_⟩
    rw [lowerSum_push hφmono hφc hφA hφB]
    exact lowerSum_congr (f := f) (α := α) (P := P)
      (P' := push hφmono hφA hφB (pull hφmono hφc hAB hφA hφB P)) rfl
      (fun i hi => (push_pull_x hφmono hφc hAB hφA hφB P i hi).symm)

theorem ch06_change_of_variable (a b A B : ℝ) (hab : a ≤ b) (hAB : A ≤ B) (f α φ : ℝ → ℝ)
    (hφmono : StrictMonoOn φ (Set.Icc A B)) (hφc : ContinuousOn φ (Set.Icc A B))
    (hφA : φ A = a) (hφB : φ B = b)
    (hα : MonotoneOn α (Set.Icc a b)) (hf : RSIntegrable a b f α) :
    RSIntegrable A B (f ∘ φ) (α ∘ φ) ∧
    RSIntegral A B (f ∘ φ) (α ∘ φ) = RSIntegral a b f α := by
  have hup : upperIntegral A B (f ∘ φ) (α ∘ φ) = upperIntegral a b f α := by
    unfold upperIntegral
    rw [upper_sets_eq hφmono hφc hAB hφA hφB]
  have hlo : lowerIntegral A B (f ∘ φ) (α ∘ φ) = lowerIntegral a b f α := by
    unfold lowerIntegral
    rw [lower_sets_eq hφmono hφc hAB hφA hφB]
  refine ⟨?_, ?_⟩
  · unfold RSIntegrable at hf ⊢
    rw [hup, hlo]
    exact hf
  · unfold RSIntegral
    exact hup

end R619

open Rudin in
theorem solution (a b A B : ℝ) (hab : a ≤ b) (hAB : A ≤ B) (f α φ : ℝ → ℝ)
    (hφmono : StrictMonoOn φ (Set.Icc A B)) (hφc : ContinuousOn φ (Set.Icc A B))
    (hφA : φ A = a) (hφB : φ B = b)
    (hα : MonotoneOn α (Set.Icc a b)) (hf : RSIntegrable a b f α) :
    RSIntegrable A B (f ∘ φ) (α ∘ φ) ∧
    RSIntegral A B (f ∘ φ) (α ∘ φ) = RSIntegral a b f α :=
  R619.ch06_change_of_variable a b A B hab hAB f α φ hφmono hφc hφA hφB hα hf
