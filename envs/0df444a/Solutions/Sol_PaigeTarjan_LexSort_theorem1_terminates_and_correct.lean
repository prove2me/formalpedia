-- Prove2me | solution 1 for PaigeTarjan.LexSort.theorem1_terminates_and_correct
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T11:15:57.889293+00:00
-- url     : https://prove2.me/submissions/d9f346c5-9bbd-4dce-84a5-e82de5581ff0

import Mathlib
import Definitions.Def_PaigeTarjan_LexSort_Basic
import Definitions.Def_PaigeTarjan_LexSort_Refine

set_option autoImplicit false

/-- `α ++ [u]` is a prefix of `l` iff `α` is and `l` has `u` at index `α.length`. -/
theorem pt6e_prefix_concat_iff {A : Type} (α l : List A) (u : A) :
    (α ++ [u]) <+: l ↔ α <+: l ∧ l[α.length]? = some u := by
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨⟨[u] ++ t, by simp⟩, ?_⟩
    simp
  · rintro ⟨⟨t, rfl⟩, h⟩
    cases t with
    | nil => simp at h
    | cons v t =>
      simp at h
      subst h
      exact ⟨t, by simp⟩

/-- A proper prefix extends by one symbol inside the longer list. -/
theorem pt6e_proper_prefix_extend {A : Type} (α l : List A) (h : α <+: l) (hne : α ≠ l) :
    ∃ u, (α ++ [u]) <+: l := by
  obtain ⟨t, rfl⟩ := h
  cases t with
  | nil => simp at hne
  | cons v t => exact ⟨v, t, by simp⟩

open PaigeTarjan.LexSort in
/-- End-marked strings are prefix-free up to equality. -/
theorem pt6e_endmarked_prefix {k n : ℕ} (x : Fin n → List (Fin (k + 1))) (hx : EndMarked x)
    (a b : Fin n) (h : x a <+: x b) : x a = x b := by
  obtain ⟨w, hw, h0⟩ := hx a
  obtain ⟨w', hw', h0'⟩ := hx b
  obtain ⟨t, ht⟩ := h
  rw [hw, hw'] at *
  have hlen := congrArg List.length ht
  simp at hlen
  rcases Nat.lt_or_ge w.length w'.length with hlt | hge
  · exfalso
    have h1 : (w ++ [0] ++ t)[w.length]? = some 0 := by simp
    rw [ht] at h1
    rw [List.getElem?_append_left hlt] at h1
    exact h0' (List.mem_of_getElem? h1)
  · have ht0 : t = [] := by
      rw [← List.length_eq_zero_iff]; omega
    subst ht0
    simpa using ht

open PaigeTarjan.LexSort in
theorem pt6e_dp_prefix {k n : ℕ} (x : Fin n → List (Fin (k + 1))) (i : Fin n) :
    dp x i <+: x i := by
  unfold dp
  split_ifs
  · exact List.prefix_refl _
  · exact List.take_prefix _ _

open PaigeTarjan.LexSort in
/-- If `dp x j` is a prefix of `x i`, then `dp x i = dp x j`. -/
theorem pt6e_dp_unique {k n : ℕ} (x : Fin n → List (Fin (k + 1))) (hx : EndMarked x)
    (i j : Fin n) (h : dp x j <+: x i) : dp x i = dp x j := by
  by_cases hdup : ∃ j', j' ≠ j ∧ x j' = x j
  · have hdj : dp x j = x j := by unfold dp; rw [if_pos hdup]
    rw [hdj] at h ⊢
    have hij := pt6e_endmarked_prefix x hx j i h
    by_cases hji : i = j
    · subst hji; exact hdj
    · unfold dp
      rw [if_pos ⟨j, fun e => hji e.symm, hij⟩]
      exact hij.symm
  · by_contra hne
    have hij : i ≠ j := by rintro rfl; exact hne rfl
    have hdj : dp x j = (x j).take (dpLength x j) := by unfold dp; rw [if_neg hdup]
    have hspec := Nat.find_spec (p := fun ℓ => ℓ = (x j).length ∨
      ∀ j', j' ≠ j → ¬ ((x j).take ℓ <+: x j')) ⟨(x j).length, Or.inl rfl⟩
    have hdl : dpLength x j = Nat.find (p := fun ℓ => ℓ = (x j).length ∨
      ∀ j', j' ≠ j → ¬ ((x j).take ℓ <+: x j')) ⟨(x j).length, Or.inl rfl⟩ := rfl
    rw [← hdl] at hspec
    rw [hdj] at h
    rcases hspec with hl | hall
    · rw [hl, List.take_length] at h
      have := pt6e_endmarked_prefix x hx j i h
      exact hdup ⟨i, hij, this.symm⟩
    · exact hall i hij h

open PaigeTarjan.LexSort in
/-- The invariant of the refinement algorithm. -/
def pt6eInv {k n : ℕ} (x : Fin n → List (Fin (k + 1))) (P : Finset (List (Fin (k + 1)))) :
    Prop :=
  (∀ α ∈ P, ∃ i, α <+: x i) ∧
  (∀ α ∈ P, ∀ i, α <+: x i → α <+: dp x i) ∧
  (∀ i, ∃ α ∈ P, α <+: x i) ∧
  (∀ α ∈ P, ∀ β ∈ P, ∀ i, α <+: x i → β <+: x i → α = β)

open Classical in
/-- The label of the block containing `i`. -/
noncomputable def pt6eLab {k n : ℕ} (x : Fin n → List (Fin (k + 1)))
    (P : Finset (List (Fin (k + 1)))) (i : Fin n) : List (Fin (k + 1)) :=
  if h : ∃ α ∈ P, α <+: x i then Classical.choose h else []

/-- The potential: total length of the labels of the blocks containing each string. -/
noncomputable def pt6ePhi {k n : ℕ} (x : Fin n → List (Fin (k + 1)))
    (P : Finset (List (Fin (k + 1)))) : ℕ :=
  ∑ i, (pt6eLab x P i).length

theorem pt6e_lab_eq {k n : ℕ} (x : Fin n → List (Fin (k + 1)))
    (P : Finset (List (Fin (k + 1))))
    (huniq : ∀ α ∈ P, ∀ β ∈ P, ∀ i, α <+: x i → β <+: x i → α = β)
    (i : Fin n) (β : List (Fin (k + 1))) (hβ : β ∈ P) (hp : β <+: x i) :
    pt6eLab x P i = β := by
  have h : ∃ α ∈ P, α <+: x i := ⟨β, hβ, hp⟩
  unfold pt6eLab
  rw [dif_pos h]
  obtain ⟨h1, h2⟩ := Classical.choose_spec h
  exact huniq _ h1 _ hβ i h2 hp

open PaigeTarjan.LexSort in
theorem pt6e_mem_children {k n : ℕ} (x : Fin n → List (Fin (k + 1)))
    (α c : List (Fin (k + 1))) :
    c ∈ children x α ↔ ∃ u, c = α ++ [u] ∧ ∃ i, (α ++ [u]) <+: x i := by
  unfold children blk
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, ⟨i, hi, hu⟩, rfl⟩
    exact ⟨u, rfl, i, (pt6e_prefix_concat_iff _ _ _).2 ⟨hi, hu⟩⟩
  · rintro ⟨u, rfl, i, hi⟩
    exact ⟨u, ⟨i, (pt6e_prefix_concat_iff _ _ _).1 hi⟩, rfl⟩

open PaigeTarjan.LexSort in
theorem pt6e_inv_step {k n : ℕ} (x : Fin n → List (Fin (k + 1)))
    (P : Finset (List (Fin (k + 1)))) (hI : pt6eInv x P)
    (α : List (Fin (k + 1))) (hα : α ∈ P) (hfin : ¬ IsFinished x α) :
    pt6eInv x (split x α P) ∧ pt6ePhi x P + 1 ≤ pt6ePhi x (split x α P) := by
  obtain ⟨ha, hb, hc, hd⟩ := hI
  have hnd : ∀ i, α ≠ dp x i := fun i e => hfin ⟨i, e⟩
  -- extension of α inside x i, for i in the block of α
  have hext : ∀ i, α <+: x i → ∃ v, (α ++ [v]) <+: dp x i := fun i hi =>
    pt6e_proper_prefix_extend _ _ (hb α hα i hi) (hnd i)
  have hmem : ∀ c, c ∈ split x α P ↔ (c ≠ α ∧ c ∈ P) ∨ c ∈ children x α := by
    intro c
    unfold split
    simp [Finset.mem_union, Finset.mem_erase]
  have hI' : pt6eInv x (split x α P) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c hc'
      rcases (hmem c).1 hc' with ⟨_, hcP⟩ | hch
      · exact ha c hcP
      · obtain ⟨u, rfl, i, hi⟩ := (pt6e_mem_children x α c).1 hch
        exact ⟨i, hi⟩
    · intro c hc' i hci
      rcases (hmem c).1 hc' with ⟨_, hcP⟩ | hch
      · exact hb c hcP i hci
      · obtain ⟨u, rfl, _, _⟩ := (pt6e_mem_children x α c).1 hch
        have h1 := (pt6e_prefix_concat_iff _ _ _).1 hci
        obtain ⟨v, hv⟩ := hext i h1.1
        have hv' : (α ++ [v]) <+: x i := hv.trans (pt6e_dp_prefix x i)
        have h2 := (pt6e_prefix_concat_iff _ _ _).1 hv'
        rw [h1.2] at h2
        have : u = v := Option.some_injective _ h2.2
        rw [this]; exact hv
    · intro i
      obtain ⟨β, hβ, hβi⟩ := hc i
      by_cases hβα : β = α
      · subst hβα
        obtain ⟨v, hv⟩ := hext i hβi
        have hv' : (β ++ [v]) <+: x i := hv.trans (pt6e_dp_prefix x i)
        exact ⟨β ++ [v], (hmem _).2 (Or.inr ((pt6e_mem_children x β _).2 ⟨v, rfl, i, hv'⟩)),
          hv'⟩
      · exact ⟨β, (hmem _).2 (Or.inl ⟨hβα, hβ⟩), hβi⟩
    · intro c hc' c' hc'' i hci hci'
      rcases (hmem c).1 hc' with ⟨hne, hcP⟩ | hch <;>
        rcases (hmem c').1 hc'' with ⟨hne', hcP'⟩ | hch'
      · exact hd c hcP c' hcP' i hci hci'
      · obtain ⟨u, rfl, _, _⟩ := (pt6e_mem_children x α c').1 hch'
        have h1 := (pt6e_prefix_concat_iff _ _ _).1 hci'
        exact absurd (hd α hα c hcP i h1.1 hci).symm hne
      · obtain ⟨u, rfl, _, _⟩ := (pt6e_mem_children x α c).1 hch
        have h1 := (pt6e_prefix_concat_iff _ _ _).1 hci
        exact absurd (hd α hα c' hcP' i h1.1 hci').symm hne'
      · obtain ⟨u, rfl, _, _⟩ := (pt6e_mem_children x α c).1 hch
        obtain ⟨u', rfl, _, _⟩ := (pt6e_mem_children x α c').1 hch'
        have h1 := (pt6e_prefix_concat_iff _ _ _).1 hci
        have h2 := (pt6e_prefix_concat_iff _ _ _).1 hci'
        rw [h1.2] at h2
        have : u = u' := Option.some_injective _ h2.2
        rw [this]
  refine ⟨hI', ?_⟩
  obtain ⟨_, _, hc', hd'⟩ := hI'
  have hterm : ∀ i, (pt6eLab x P i).length ≤ (pt6eLab x (split x α P) i).length ∧
      (α <+: x i → (pt6eLab x P i).length < (pt6eLab x (split x α P) i).length) := by
    intro i
    obtain ⟨β, hβ, hβi⟩ := hc i
    have hl : pt6eLab x P i = β := pt6e_lab_eq x P hd i β hβ hβi
    by_cases hβα : β = α
    · subst hβα
      obtain ⟨v, hv⟩ := hext i hβi
      have hv' : (β ++ [v]) <+: x i := hv.trans (pt6e_dp_prefix x i)
      have hmv : β ++ [v] ∈ split x β P :=
        (hmem _).2 (Or.inr ((pt6e_mem_children x β _).2 ⟨v, rfl, i, hv'⟩))
      have hl' := pt6e_lab_eq x _ hd' i _ hmv hv'
      rw [hl, hl']
      simp
    · have hmv : β ∈ split x α P := (hmem _).2 (Or.inl ⟨hβα, hβ⟩)
      have hl' := pt6e_lab_eq x _ hd' i _ hmv hβi
      rw [hl, hl']
      refine ⟨le_refl _, fun hαi => ?_⟩
      exact absurd (hd β hβ α hα i hβi hαi) hβα
  obtain ⟨i0, hi0⟩ := ha α hα
  unfold pt6ePhi
  have hlt : ∑ i, (pt6eLab x P i).length < ∑ i, (pt6eLab x (split x α P) i).length :=
    Finset.sum_lt_sum (fun i _ => (hterm i).1) ⟨i0, Finset.mem_univ _, (hterm i0).2 hi0⟩
  omega

open PaigeTarjan.LexSort in
theorem pt6e_phi_le {k n : ℕ} (x : Fin n → List (Fin (k + 1)))
    (P : Finset (List (Fin (k + 1)))) (hI : pt6eInv x P) :
    pt6ePhi x P ≤ mPrime x := by
  obtain ⟨_, hb, hc, hd⟩ := hI
  unfold pt6ePhi mPrime
  refine Finset.sum_le_sum (fun i _ => ?_)
  obtain ⟨β, hβ, hβi⟩ := hc i
  rw [pt6e_lab_eq x P hd i β hβ hβi]
  exact (hb β hβ i hβi).length_le

open PaigeTarjan.LexSort in
theorem solution {k n : ℕ} (x : Fin n → List (Fin (k + 1)))
    (hn : 0 < n) (hx : EndMarked x) (K : ℕ)
    (Ps : Fin (K + 1) → Finset (List (Fin (k + 1)))) (hrun : IsRun x K Ps) :
    K ≤ mPrime x ∧
    ((∀ α ∈ Ps (Fin.last K), IsFinished x α) → Ps (Fin.last K) = finishedLabels x) := by
  obtain ⟨h0, hstep⟩ := hrun
  have key : ∀ j : ℕ, ∀ hj : j < K + 1, pt6eInv x (Ps ⟨j, hj⟩) ∧ j ≤ pt6ePhi x (Ps ⟨j, hj⟩) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have : (⟨0, hj⟩ : Fin (K + 1)) = 0 := rfl
      rw [this, h0]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, Nat.zero_le _⟩
      · intro α hα
        rw [Finset.mem_singleton] at hα
        subst hα
        exact ⟨⟨0, hn⟩, List.nil_prefix⟩
      · intro α hα i _
        rw [Finset.mem_singleton] at hα
        subst hα
        exact List.nil_prefix
      · intro i
        exact ⟨[], Finset.mem_singleton_self _, List.nil_prefix⟩
      · intro α hα β hβ i _ _
        rw [Finset.mem_singleton] at hα hβ
        rw [hα, hβ]
    | succ j ih =>
      intro hj
      have hjK : j < K := by omega
      obtain ⟨hI, hphi⟩ := ih (by omega)
      obtain ⟨α, hα, hfin, hP'⟩ := hstep ⟨j, hjK⟩
      have e1 : (Fin.castSucc (⟨j, hjK⟩ : Fin K)) = ⟨j, by omega⟩ := rfl
      have e2 : (Fin.succ (⟨j, hjK⟩ : Fin K)) = ⟨j + 1, hj⟩ := rfl
      rw [e1] at hα hP'
      rw [e2] at hP'
      rw [hP']
      obtain ⟨hI', hlt⟩ := pt6e_inv_step x _ hI α hα hfin
      exact ⟨hI', by omega⟩
  obtain ⟨hI, hphi⟩ := key K (Nat.lt_succ_self K)
  have elast : (⟨K, Nat.lt_succ_self K⟩ : Fin (K + 1)) = Fin.last K := rfl
  rw [elast] at hI hphi
  refine ⟨le_trans hphi (pt6e_phi_le x _ hI), ?_⟩
  intro hall
  obtain ⟨_, hb, hc, _⟩ := hI
  ext β
  unfold finishedLabels
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hβ
    obtain ⟨i, hi⟩ := hall β hβ
    exact ⟨i, hi.symm⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨α, hα, hαi⟩ := hc i
    obtain ⟨j, hj⟩ := hall α hα
    have h1 : α <+: dp x i := hb α hα i hαi
    have h2 : dp x j <+: x i := by rw [← hj]; exact hαi
    have h3 := pt6e_dp_unique x hx i j h2
    rw [h3, ← hj]
    exact hα
