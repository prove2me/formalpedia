-- Prove2me | solution 1 for SymmetricPSM1041.ORLowerBound.or_and_superlinear_total_communication
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:07:12.228114+00:00
-- url     : https://prove2.me/submissions/85b65495-9067-4934-be18-9c8c79446e67

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions
import Theorems.Thm_SymmetricPSM1041_ORLowerBound_constant_alphabet_or_impossible
import Theorems.Thm_SymmetricPSM1041_ORLowerBound_support_restriction_lifting

open SymmetricPSM1041.ORLowerBound

private lemma constantOrImpossibleOfFintype (K N : ℕ)
    (hN : ∀ n : ℕ, N ≤ n → ∀ P : PSM (Fin n),
      (∀ i, (localAlphabet P i).card ≤ K) →
      ¬ (PerfectCorrect P orFunction ∧ SupportPrivate P orFunction))
    (ι : Type*) [Fintype ι] (hcardι : N ≤ Fintype.card ι) (P : PSM ι)
    (halpha : ∀ i, (localAlphabet P i).card ≤ K)
    (hc : PerfectCorrect P orFunction) (hp : SupportPrivate P orFunction) : False := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let pull (x : Fin (Fintype.card ι) → Bool) : ι → Bool := fun i => x (e.symm i)
  let Q : PSM (Fin (Fintype.card ι)) := {
    seedCount := P.seedCount
    seedCount_pos := P.seedCount_pos
    alphabet := fun j => P.alphabet (e j)
    message := fun j b r => P.message (e j) b r
    decode := fun t => P.decode (fun i =>
      ⟨(t (e.symm i)).val, by simpa using (t (e.symm i)).property⟩) }
  have hor (x : Fin (Fintype.card ι) → Bool) : orFunction (pull x) = orFunction x := by
    unfold orFunction
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, hi⟩
    · rintro ⟨j, hj⟩
      exact ⟨e j, by simpa [pull] using hj⟩
  have hQc : PerfectCorrect Q orFunction := by
    intro x r
    change P.decode (fun i =>
      ⟨(P.message (e (e.symm i)) (x (e.symm i)) r).val, _⟩) = orFunction x
    have ht : (fun i =>
        ⟨(P.message (e (e.symm i)) (x (e.symm i)) r).val, by
          simpa using (P.message (e (e.symm i)) (x (e.symm i)) r).property⟩) =
        transcript P (pull x) r := by
      funext i
      apply Subtype.ext
      change (P.message (e (e.symm i)) (x (e.symm i)) r).val =
        (P.message i (x (e.symm i)) r).val
      rw [e.apply_symm_apply]
    rw [ht, hc (pull x) r, hor]
  have hQp : SupportPrivate Q orFunction := by
    intro x y hxy
    apply Set.ext
    intro t
    constructor
    · rintro ⟨r, rfl⟩
      have hfull : orFunction (pull x) = orFunction (pull y) := by simpa [hor] using hxy
      have hs := hp (pull x) (pull y) hfull
      have hm : transcript P (pull x) r ∈ transcriptSupport P (pull x) := ⟨r, rfl⟩
      rw [hs] at hm
      obtain ⟨r', hr'⟩ := hm
      refine ⟨r', ?_⟩
      funext j
      have hj := congrFun hr' (e j)
      simpa [transcript, Q, pull] using hj
    · rintro ⟨r, rfl⟩
      have hfull : orFunction (pull y) = orFunction (pull x) := by simpa [hor] using hxy.symm
      have hs := hp (pull y) (pull x) hfull
      have hm : transcript P (pull y) r ∈ transcriptSupport P (pull y) := ⟨r, rfl⟩
      rw [hs] at hm
      obtain ⟨r', hr'⟩ := hm
      refine ⟨r', ?_⟩
      funext j
      have hj := congrFun hr' (e j)
      simpa [transcript, Q, pull] using hj
  have hQa (j : Fin (Fintype.card ι)) : (localAlphabet Q j).card ≤ K := by
    have heq : localAlphabet Q j = localAlphabet P (e j) := by
      simp [localAlphabet, Q]
    rw [heq]
    exact halpha (e j)
  exact (hN (Fintype.card ι) hcardι Q hQa) ⟨hQc, hQp⟩

private lemma andProtocolToOr {n : ℕ} (P : PSM (Fin n))
    (hc : PerfectCorrect P andFunction) (hp : SupportPrivate P andFunction) :
    ∃ Q : PSM (Fin n), PerfectCorrect Q orFunction ∧ SupportPrivate Q orFunction ∧
      ∀ (x : Fin n → Bool) (r : Fin Q.seedCount),
        ∃ rP : Fin P.seedCount,
          transcriptLength Q x r = transcriptLength P (fun i => !(x i)) rP := by
  classical
  let negInput (x : Fin n → Bool) : Fin n → Bool := fun i => !(x i)
  let Q : PSM (Fin n) := {
    seedCount := P.seedCount
    seedCount_pos := P.seedCount_pos
    alphabet := P.alphabet
    message := fun i b r => P.message i (!b) r
    decode := fun t => !(P.decode t) }
  have hdeMorgan (x : Fin n → Bool) : (!(andFunction (negInput x))) = orFunction x := by
    by_cases h : ∃ i, x i = true
    · have hor : orFunction x = true := by
        unfold orFunction
        simp [h]
      obtain ⟨i, hi⟩ := h
      have hand : andFunction (negInput x) = false := by
        unfold andFunction
        rw [decide_eq_false_iff_not]
        intro hall
        have hh := hall i
        simpa [negInput, hi] using hh
      simp [hand, hor]
    · have hall : ∀ i, x i = false := by
        intro i
        cases hx : x i <;> simp_all
      have hor : orFunction x = false := by
        unfold orFunction
        simp [h]
      have hand : andFunction (negInput x) = true := by
        unfold andFunction
        simp [negInput, hall]
      simp [hand, hor]
  have hQc : PerfectCorrect Q orFunction := by
    intro x r
    change (!(P.decode (transcript P (negInput x) r))) = orFunction x
    rw [hc (negInput x) r]
    exact hdeMorgan x
  have hQp : SupportPrivate Q orFunction := by
    intro x y hxy
    have hfull : andFunction (negInput x) = andFunction (negInput y) := by
      apply Bool.not_inj
      rw [hdeMorgan, hdeMorgan, hxy]
    have hs := hp (negInput x) (negInput y) hfull
    exact hs
  refine ⟨Q, hQc, hQp, ?_⟩
  intro x r
  refine ⟨⟨r.val, by simpa [Q] using r.isLt⟩, ?_⟩
  simp [transcriptLength, Q, negInput]

theorem solution :
    ∀ A : ℝ, 0 < A → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ f : (Fin n → Bool) → Bool, (f = orFunction ∨ f = andFunction) →
      ∀ P : PSM (Fin n), PerfectCorrect P f → SupportPrivate P f →
        ∃ (x : Fin n → Bool) (r : Fin P.seedCount),
          A * (n : ℝ) ≤ (transcriptLength P x r : ℝ) := by
  intro A hA
  obtain ⟨C, hC⟩ := exists_nat_gt (2 * A)
  have hCpos : 1 ≤ C := by
    have : 0 < (C : ℝ) := lt_of_lt_of_le (mul_pos (by norm_num) hA) hC.le
    exact_mod_cast this
  let B := C - 1
  have hBC : B + 1 = C := by omega
  let K := 2 ^ C - 1
  obtain ⟨s, hs, hconst⟩ := constant_alphabet_or_impossible K
  let N := 2 * s
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro n hn f hf P hc hp
  have hsn : s ≤ n := by dsimp [N] at hn; omega
  have hrestr : ∀ I : Finset (Fin n), s ≤ I.card → ∃ z : Fin n → Bool,
      IndividualLowerBound .support (restrictFunction orFunction I z) (B + 1) := by
    intro I hI
    let z : Fin n → Bool := fun _ => false
    refine ⟨z, ?_⟩
    intro Q hQc hQp
    have hfun : restrictFunction orFunction I z = orFunction := by
      funext y
      simp [restrictFunction, orFunction, z]
    rw [hfun] at hQc hQp
    by_contra hnone
    push_neg at hnone
    have hall : ∀ i, (localAlphabet Q i).card ≤ K := by
      intro i
      have hi := hnone i
      dsimp [K]
      rw [hBC] at hi
      omega
    exact constantOrImpossibleOfFintype K s hconst I (by simpa using hI) Q hall hQc hQp
  have orLower (Q : PSM (Fin n)) (hQc : PerfectCorrect Q orFunction)
      (hQp : SupportPrivate Q orFunction) :
      ∃ (x : Fin n → Bool) (r : Fin Q.seedCount),
        A * (n : ℝ) ≤ (transcriptLength Q x r : ℝ) := by
    obtain ⟨x, r, hlen⟩ := support_restriction_lifting orFunction s B hs hsn hrestr Q hQc hQp
    refine ⟨x, r, ?_⟩
    have hn2s : 2 * s ≤ n := by simpa [N] using hn
    have hhalf : n ≤ 2 * (n - s + 1) := by omega
    have hnat : C * n ≤ 2 * transcriptLength Q x r := by
      have hlenC : C * (n - s + 1) ≤ transcriptLength Q x r := by
        simpa [hBC] using hlen
      calc
        C * n ≤ C * (2 * (n - s + 1)) := Nat.mul_le_mul_left C hhalf
        _ = 2 * (C * (n - s + 1)) := by
          simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ ≤ 2 * transcriptLength Q x r := Nat.mul_le_mul_left 2 hlenC
    have hnat' : (C : ℝ) * (n : ℝ) ≤
        2 * (transcriptLength Q x r : ℝ) := by exact_mod_cast hnat
    have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
    nlinarith
  rcases hf with rfl | rfl
  · exact orLower P hc hp
  · obtain ⟨Q, hQc, hQp, hlenQ⟩ := andProtocolToOr P hc hp
    obtain ⟨x, r, hlen⟩ := orLower Q hQc hQp
    obtain ⟨rP, hlenEq⟩ := hlenQ x r
    refine ⟨fun i => !(x i), rP, ?_⟩
    rw [hlenEq] at hlen
    exact hlen
