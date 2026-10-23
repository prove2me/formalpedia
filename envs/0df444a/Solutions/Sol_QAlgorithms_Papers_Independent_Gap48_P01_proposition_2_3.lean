-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P01.proposition_2_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:17:13.660758+00:00
-- url     : https://prove2.me/submissions/68495e76-87aa-4768-9ef8-fd5c5906b5fc

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01
noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

namespace X8B

variable {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ)

lemma rel {a b : FreeAlgebra R (CyclotomicLetter n)} (h : NonsplitBMWRel P n a b) :
    presentationMap P n a = presentationMap P n b :=
  RingQuot.mkAlgHom_rel R h

lemma x_xi (i : ℕ) (hi : 1 ≤ i ∧ i < n) : X P n i false * X P n i true = 1 := by
  have := rel P n (NonsplitBMWRel.invL i hi); simpa [X, map_mul] using this

lemma xi_x (i : ℕ) (hi : 1 ≤ i ∧ i < n) : X P n i true * X P n i false = 1 := by
  have := rel P n (NonsplitBMWRel.invR i hi); simpa [X, map_mul] using this

lemma nearL (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 = j ∨ j + 1 = i) :
    X P n i false * X P n j false * E P n i = E P n j * E P n i := by
  have := rel P n (NonsplitBMWRel.nearL i j hi hj hd); simpa [X, E, map_mul] using this

lemma nearR (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 = j ∨ j + 1 = i) :
    E P n j * X P n i false * X P n j false = E P n j * E P n i := by
  have := rel P n (NonsplitBMWRel.nearR i j hi hj hd); simpa [X, E, map_mul] using this

lemma tripleE (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 = j ∨ j + 1 = i) :
    E P n i * E P n j * E P n i = E P n i := by
  have := rel P n (NonsplitBMWRel.tripleE i j hi hj hd); simpa [E, map_mul] using this

lemma eeFar (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 < j ∨ j + 1 < i) :
    E P n i * E P n j = E P n j * E P n i := by
  have := rel P n (NonsplitBMWRel.eeFar i j hi hj hd); simpa [E, map_mul] using this

lemma xeFar (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n) (hd : i + 1 < j ∨ j + 1 < i) :
    X P n i false * E P n j = E P n j * X P n i false := by
  have := rel P n (NonsplitBMWRel.xeFar i j hi hj hd); simpa [X, E, map_mul] using this

lemma braid (i : ℕ) (hi : 1 ≤ i ∧ i + 1 < n) :
    X P n i false * X P n (i+1) false * X P n i false =
      X P n (i+1) false * X P n i false * X P n (i+1) false := by
  have := rel P n (NonsplitBMWRel.braid i hi); simpa [X, map_mul] using this

lemma ye (i : ℕ) (hi : 1 < i ∧ i < n) : Y P n false * E P n i = E P n i * Y P n false := by
  have := rel P n (NonsplitBMWRel.ye i hi); simpa [Y, E, map_mul] using this

lemma jm_comm (i : ℕ) (hi : 1 ≤ i) : ∀ j, i + 1 ≤ j → j < n →
    JM P n false i * E P n j = E P n j * JM P n false i := by
  induction i with
  | zero => omega
  | succ m ih =>
    intro j hj hjn
    rcases m with _ | m
    · exact ye P n j ⟨by omega, hjn⟩
    · have h1 := ih (by omega) j (by omega) hjn
      have h2 := xeFar P n (m+1) j ⟨by omega, by omega⟩ ⟨by omega, hjn⟩ (Or.inl (by omega))
      show X P n (m+1) false * JM P n false (m+1) * X P n (m+1) false * E P n j =
        E P n j * (X P n (m+1) false * JM P n false (m+1) * X P n (m+1) false)
      rw [mul_assoc, h2, ← mul_assoc, mul_assoc _ (JM P n false (m+1)), h1, ← mul_assoc, h2]
      simp only [mul_assoc]

theorem x8_main :
    (∀ i, 1 ≤ i → i+2 < n → ∀ g : ℕ → NonsplitBMW P n,
      (g = (fun j => X P n j false) ∨ g = E P n ∨ g = JM P n false) →
      E P n i * E P n (i+1) * E P n (i+2) * g i =
        g (i+2) * E P n i * E P n (i+1) * E P n (i+2)) ∧
    (∀ i, 1 ≤ i → i+1 < n → ∀ g : ℕ → NonsplitBMW P n,
      (g = (fun j => X P n j false) ∨ g = E P n) →
      X P n i false * X P n (i+1) false * g i =
        g (i+1) * X P n i false * X P n (i+1) false) := by
  refine ⟨?_, ?_⟩
  · intro i hi hin g hg
    have r0 : 1 ≤ i ∧ i < n := ⟨hi, by omega⟩
    have r1 : 1 ≤ i+1 ∧ i+1 < n := ⟨by omega, by omega⟩
    have r2 : 1 ≤ i+2 ∧ i+2 < n := ⟨by omega, hin⟩
    have t0 := tripleE P n i (i+1) r0 r1 (Or.inl rfl)
    have t2 := tripleE P n (i+2) (i+1) r2 r1 (Or.inr rfl)
    rcases hg with rfl | rfl | rfl
    · -- g = X
      have hA : E P n (i+1) * X P n i false = E P n (i+1) * E P n i * X P n (i+1) true := by
        have h := nearR P n i (i+1) r0 r1 (Or.inl rfl)
        rw [← h, mul_assoc _ (X P n (i+1) false), x_xi P n (i+1) r1, mul_one]
      have hB : X P n (i+2) false * E P n (i+1) = X P n (i+1) true * E P n (i+2) * E P n (i+1) := by
        have h := nearL P n (i+1) (i+2) r1 r2 (Or.inl rfl)
        rw [mul_assoc, ← h, ← mul_assoc, ← mul_assoc, xi_x P n (i+1) r1, one_mul]
      have hC := xeFar P n i (i+2) r0 r2 (Or.inl (by omega))
      have hD := xeFar P n (i+2) i r2 r0 (Or.inr (by omega))
      set e0 := E P n i
      set e1 := E P n (i+1)
      set e2 := E P n (i+2)
      set x0 := X P n i false
      set x2 := X P n (i+2) false
      set y1 := X P n (i+1) true
      show e0 * e1 * e2 * x0 = x2 * e0 * e1 * e2
      calc e0 * e1 * e2 * x0 = e0 * (e1 * x0) * e2 := by rw [mul_assoc _ e2, ← hC]; simp only [mul_assoc]
        _ = e0 * y1 * e2 := by rw [hA, ← mul_assoc, ← mul_assoc, t0]
        _ = e0 * (x2 * e1) * e2 := by rw [hB]; simp only [mul_assoc]; rw [← mul_assoc e2 e1 e2, t2]
        _ = x2 * e0 * e1 * e2 := by rw [← mul_assoc, ← hD]
    · -- g = E
      have hF := eeFar P n (i+2) i r2 r0 (Or.inr (by omega))
      set e0 := E P n i
      set e1 := E P n (i+1)
      set e2 := E P n (i+2)
      show e0 * e1 * e2 * e0 = e2 * e0 * e1 * e2
      calc e0 * e1 * e2 * e0 = e0 * e1 * e0 * e2 := by rw [mul_assoc _ e2, hF, ← mul_assoc]
        _ = e0 * e2 := by rw [t0]
        _ = e0 * (e2 * e1 * e2) := by rw [t2]
        _ = e2 * e0 * e1 * e2 := by rw [hF]; simp only [mul_assoc]
    · -- g = JM
      obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      have hJ : JM P n false (m+1+2) = X P n (m+1+1) false * X P n (m+1) false * JM P n false (m+1) *
          X P n (m+1) false * X P n (m+1+1) false := by
        show X P n (m+2) false * (X P n (m+1) false * JM P n false (m+1) * X P n (m+1) false) *
          X P n (m+2) false = _
        simp only [mul_assoc]
      have c1 := jm_comm P n (m+1) (by omega) (m+1+1) (by omega) r1.2
      have c2 := jm_comm P n (m+1) (by omega) (m+1+2) (by omega) r2.2
      have nL := nearL P n (m+1) (m+1+1) r0 r1 (Or.inl rfl)
      have nL' := nearL P n (m+1+1) (m+1) r1 r0 (Or.inr rfl)
      have t1 := tripleE P n (m+1+1) (m+1) r1 r0 (Or.inr rfl)
      rw [hJ]
      set e0 := E P n (m+1)
      set e1 := E P n (m+1+1)
      set e2 := E P n (m+1+2)
      set J := JM P n false (m+1)
      set x0 := X P n (m+1) false
      set x1 := X P n (m+1+1) false
      calc e0 * e1 * e2 * J = e0 * e1 * J * e2 := by rw [mul_assoc _ e2, ← c2, ← mul_assoc]
        _ = x1 * x0 * e1 * J * e2 := by rw [nL']
        _ = x1 * x0 * J * (e1 * e0 * e1) * e2 := by
          rw [t1, mul_assoc (x1 * x0), ← c1]; simp only [mul_assoc]
        _ = x1 * x0 * J * x0 * x1 * e0 * e1 * e2 := by
          rw [← nL]; simp only [mul_assoc]
  · intro i hi hin g hg
    have r0 : 1 ≤ i ∧ i < n := ⟨hi, by omega⟩
    have r1 : 1 ≤ i+1 ∧ i+1 < n := ⟨by omega, hin⟩
    rcases hg with rfl | rfl
    · exact braid P n i ⟨hi, hin⟩
    · show _ * _ * E P n i = E P n (i+1) * _ * _
      rw [nearL P n i (i+1) r0 r1 (Or.inl rfl), nearR P n i (i+1) r0 r1 (Or.inl rfl)]

end X8B

end QAlgorithms.Papers.Independent.Gap48.P01

open QAlgorithms.Papers.Independent.Gap48.P01 in
theorem solution {R : Type*} [CommRing R] {k : ℕ} (P : NonsplitParameters R k) (n : ℕ) :
    (∀ i, 1 ≤ i → i+2 < n → ∀ g : ℕ → NonsplitBMW P n,
      (g = (fun j => X P n j false) ∨ g = E P n ∨ g = JM P n false) →
      E P n i * E P n (i+1) * E P n (i+2) * g i =
        g (i+2) * E P n i * E P n (i+1) * E P n (i+2)) ∧
    (∀ i, 1 ≤ i → i+1 < n → ∀ g : ℕ → NonsplitBMW P n,
      (g = (fun j => X P n j false) ∨ g = E P n) →
      X P n i false * X P n (i+1) false * g i =
        g (i+1) * X P n i false * X P n (i+1) false) :=
  X8B.x8_main P n
