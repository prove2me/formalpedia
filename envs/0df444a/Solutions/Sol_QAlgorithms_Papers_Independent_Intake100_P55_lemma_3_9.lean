-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P55.lemma_3_9
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T11:36:15.126601+00:00
-- url     : https://prove2.me/submissions/1229c3b9-9425-4ee0-81f6-96997fcd347d

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55
noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Mon
variable {A : Type*} [Monoid A]

theorem AuxL_bws (h : ℕ → A) (a m : ℕ) : backward h a (m+1) = h (a+m) * backward h a m := by
  simp [backward, List.range_succ]

theorem AuxL_fws (h : ℕ → A) (a m : ℕ) : forward h a (m+1) = forward h a m * h (a+m) := by
  simp [forward, List.range_succ]

theorem AuxL_bwc (h : ℕ → A) (y : A) : ∀ m, (∀ j, 1 ≤ j → j ≤ m → y * h j = h j * y) →
    y * backward h 1 m = backward h 1 m * y := by
  intro m
  induction m with
  | zero => intro _; simp [backward]
  | succ m ih =>
    intro hy
    rw [AuxL_bws]
    have h1 := hy (1+m) (by omega) (by omega)
    have h2 := ih (fun j hj hjm => hy j hj (by omega))
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem AuxL_fwc (h : ℕ → A) (y : A) : ∀ m, (∀ j, 1 ≤ j → j ≤ m → y * h j = h j * y) →
    y * forward h 1 m = forward h 1 m * y := by
  intro m
  induction m with
  | zero => intro _; simp [forward]
  | succ m ih =>
    intro hy
    rw [AuxL_fws]
    have h1 := hy (1+m) (by omega) (by omega)
    have h2 := ih (fun j hj hjm => hy j hj (by omega))
    rw [← mul_assoc, h2, mul_assoc, h1, mul_assoc]

theorem AuxL_bw (h X Y : ℕ → A) (N : ℕ)
    (hX : ∀ i j, 1 ≤ i → i + 2 ≤ j → j < N → X i * h j = h j * X i)
    (hY : ∀ i j, 1 ≤ j → j + 2 ≤ i → i < N → Y i * h j = h j * Y i)
    (hXY : ∀ i, 1 ≤ i → i + 1 < N → X i * (h (i+1) * h i) = (h (i+1) * h i) * Y (i+1)) :
    ∀ m, m < N → ∀ i, 1 ≤ i → i < m → X i * backward h 1 m = backward h 1 m * Y (i+1) := by
  intro m
  induction m with
  | zero => intro _ i _ him; omega
  | succ m ih =>
    intro hm i hi him
    rw [AuxL_bws]
    rcases Nat.lt_or_ge i m with hlt | hge
    · rw [← mul_assoc, hX i (1+m) hi (by omega) (by omega), mul_assoc,
        ih (by omega) i hi hlt, mul_assoc]
    · obtain rfl : i = m := by omega
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      rw [AuxL_bws]
      have e1 : 1 + (k+1) = k + 1 + 1 := by omega
      have e2 : 1 + k = k + 1 := by omega
      rw [e1, e2]
      have hc := AuxL_bwc h (Y (k+1+1)) k (fun j hj hjk => hY (k+1+1) j hj (by omega) (by omega))
      calc X (k+1) * (h (k+1+1) * (h (k+1) * backward h 1 k))
          = X (k+1) * (h (k+1+1) * h (k+1)) * backward h 1 k := by simp only [mul_assoc]
        _ = (h (k+1+1) * h (k+1)) * Y (k+1+1) * backward h 1 k := by
            rw [hXY (k+1) (by omega) (by omega)]
        _ = (h (k+1+1) * h (k+1)) * (backward h 1 k * Y (k+1+1)) := by rw [mul_assoc, hc]
        _ = h (k+1+1) * (h (k+1) * backward h 1 k) * Y (k+1+1) := by simp only [mul_assoc]

theorem AuxL_fw (h X Y : ℕ → A) (N : ℕ)
    (hX : ∀ i j, 1 ≤ i → i + 2 ≤ j → j < N → X i * h j = h j * X i)
    (hY : ∀ i j, 1 ≤ j → j + 2 ≤ i → i < N → Y i * h j = h j * Y i)
    (hYX : ∀ i, 1 ≤ i → i + 1 < N → Y (i+1) * (h i * h (i+1)) = (h i * h (i+1)) * X i) :
    ∀ m, m < N → ∀ i, 1 ≤ i → i < m → Y (i+1) * forward h 1 m = forward h 1 m * X i := by
  intro m
  induction m with
  | zero => intro _ i _ him; omega
  | succ m ih =>
    intro hm i hi him
    rw [AuxL_fws]
    rcases Nat.lt_or_ge i m with hlt | hge
    · rw [← mul_assoc, ih (by omega) i hi hlt, mul_assoc,
        hX i (1+m) hi (by omega) (by omega), mul_assoc]
    · obtain rfl : i = m := by omega
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      rw [AuxL_fws]
      have e1 : 1 + (k+1) = k + 1 + 1 := by omega
      have e2 : 1 + k = k + 1 := by omega
      rw [e1, e2]
      have hc := AuxL_fwc h (Y (k+1+1)) k (fun j hj hjk => hY (k+1+1) j hj (by omega) (by omega))
      calc Y (k+1+1) * (forward h 1 k * h (k+1) * h (k+1+1))
          = (Y (k+1+1) * forward h 1 k) * (h (k+1) * h (k+1+1)) := by simp only [mul_assoc]
        _ = forward h 1 k * (Y (k+1+1) * (h (k+1) * h (k+1+1))) := by rw [hc, mul_assoc]
        _ = forward h 1 k * ((h (k+1) * h (k+1+1)) * X (k+1)) := by
            rw [hYX (k+1) (by omega) (by omega)]
        _ = forward h 1 k * h (k+1) * h (k+1+1) * X (k+1) := by simp only [mul_assoc]

theorem AuxL_conj {a a' b b' c : A} (ha : a' * a = 1) (hb : b * b' = 1) (h : a * c = c * b) :
    a' * c = c * b' := by
  calc a' * c = a' * c * (b * b') := by rw [hb, mul_one]
    _ = a' * (c * b) * b' := by simp only [mul_assoc]
    _ = a' * (a * c) * b' := by rw [h]
    _ = (a' * a) * c * b' := by simp only [mul_assoc]
    _ = c * b' := by rw [ha, one_mul]

end Mon

section Rels
variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R) (aff : Bool) (n : ℕ)

theorem AuxL_invL (i : ℕ) (hi : BMWIndex n i) :
    ghCrossing P q aff n i false * ghCrossing P q aff n i true = 1 := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.invL (P := P) (q := q) (aff := aff) (n := n) i hi)
  simpa only [ghCrossing, presentation, map_mul, map_one] using this

theorem AuxL_invR (i : ℕ) (hi : BMWIndex n i) :
    ghCrossing P q aff n i true * ghCrossing P q aff n i false = 1 := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.invR (P := P) (q := q) (aff := aff) (n := n) i hi)
  simpa only [ghCrossing, presentation, map_mul, map_one] using this

theorem AuxL_braid (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 < n) :
    ghCrossing P q aff n i false * ghCrossing P q aff n (i+1) false * ghCrossing P q aff n i false =
    ghCrossing P q aff n (i+1) false * ghCrossing P q aff n i false * ghCrossing P q aff n (i+1) false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.braid (P := P) (q := q) (aff := aff) (n := n) i h1 h2)
  simpa only [ghCrossing, presentation, map_mul] using this

theorem AuxL_gg (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (hd : i + 1 < j ∨ j + 1 < i) :
    ghCrossing P q aff n i false * ghCrossing P q aff n j false =
    ghCrossing P q aff n j false * ghCrossing P q aff n i false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.ggFar (P := P) (q := q) (aff := aff) (n := n) i j hi hj hd)
  simpa only [ghCrossing, presentation, map_mul] using this

theorem AuxL_ge (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (hd : i + 1 < j ∨ j + 1 < i) :
    ghCrossing P q aff n i false * ghContraction P q aff n j =
    ghContraction P q aff n j * ghCrossing P q aff n i false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.geFar (P := P) (q := q) (aff := aff) (n := n) i j hi hj hd)
  simpa only [ghCrossing, ghContraction, presentation, map_mul] using this

theorem AuxL_ee (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (hd : i + 1 < j ∨ j + 1 < i) :
    ghContraction P q aff n i * ghContraction P q aff n j =
    ghContraction P q aff n j * ghContraction P q aff n i := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.eeFar (P := P) (q := q) (aff := aff) (n := n) i j hi hj hd)
  simpa only [ghContraction, presentation, map_mul] using this

theorem AuxL_tL (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (ha : BMWAdjacent i j) :
    ghCrossing P q aff n i false * ghCrossing P q aff n j false * ghContraction P q aff n i =
    ghContraction P q aff n j * ghContraction P q aff n i := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.tangleL (P := P) (q := q) (aff := aff) (n := n) i j hi hj ha)
  simpa only [ghCrossing, ghContraction, presentation, map_mul] using this

theorem AuxL_tR (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (ha : BMWAdjacent i j) :
    ghContraction P q aff n i * ghCrossing P q aff n j false * ghCrossing P q aff n i false =
    ghContraction P q aff n i * ghContraction P q aff n j := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.tangleR (P := P) (q := q) (aff := aff) (n := n) i j hi hj ha)
  simpa only [ghCrossing, ghContraction, presentation, map_mul] using this

end Rels

theorem _root_.solution {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R) (aff : Bool) (n : ℕ) :
    (∀ i, 1 ≤ i → i+1 < n → ∀ inv : Bool,
      ghCrossing P q aff n i inv * (ghCrossing P q aff n (i+1) false * ghCrossing P q aff n i false) =
      (ghCrossing P q aff n (i+1) false * ghCrossing P q aff n i false) * ghCrossing P q aff n (i+1) inv) ∧
    (∀ i, 1 ≤ i → i+1 < n →
      ghContraction P q aff n i * (ghCrossing P q aff n (i+1) false * ghCrossing P q aff n i false) =
      (ghCrossing P q aff n (i+1) false * ghCrossing P q aff n i false) * ghContraction P q aff n (i+1)) ∧
    (∀ i, 1 ≤ i → i+2 < n →
      ghCrossing P q aff n i false * ghCrossing P q aff n (i+1) false * ghContraction P q aff n i * ghContraction P q aff n (i+2) =
      ghCrossing P q aff n (i+2) false * ghCrossing P q aff n (i+1) false * ghContraction P q aff n i * ghContraction P q aff n (i+2)) ∧
    (∀ i m, 1 ≤ i → i < m → m < n → ∀ inv : Bool,
      ghCrossing P q aff n i inv * backward (fun j => ghCrossing P q aff n j false) 1 m =
        backward (fun j => ghCrossing P q aff n j false) 1 m * ghCrossing P q aff n (i+1) inv ∧
      ghCrossing P q aff n (i+1) inv * forward (fun j => ghCrossing P q aff n j false) 1 m =
        forward (fun j => ghCrossing P q aff n j false) 1 m * ghCrossing P q aff n i inv) ∧
    (∀ i m, 1 ≤ i → i < m → m < n →
      ghContraction P q aff n i * backward (fun j => ghCrossing P q aff n j false) 1 m =
        backward (fun j => ghCrossing P q aff n j false) 1 m * ghContraction P q aff n (i+1) ∧
      ghContraction P q aff n (i+1) * forward (fun j => ghCrossing P q aff n j false) 1 m =
        forward (fun j => ghCrossing P q aff n j false) 1 m * ghContraction P q aff n i) := by
  set G : ℕ → OrdinaryAffineBMW P q aff n := fun j => ghCrossing P q aff n j false with hGdef
  set E : ℕ → OrdinaryAffineBMW P q aff n := fun j => ghContraction P q aff n j with hEdef
  have bF : ∀ i, 1 ≤ i → i + 1 < n →
      G i * (G (i+1) * G i) = (G (i+1) * G i) * G (i+1) := by
    intro i h1 h2
    simp only [hGdef]
    rw [← mul_assoc]; exact AuxL_braid P q aff n i h1 h2
  have bR : ∀ i, 1 ≤ i → i + 1 < n →
      G (i+1) * (G i * G (i+1)) = (G i * G (i+1)) * G i := by
    intro i h1 h2
    simp only [hGdef]
    rw [← mul_assoc]; exact (AuxL_braid P q aff n i h1 h2).symm
  have c2 : ∀ i, 1 ≤ i → i + 1 < n →
      E i * (G (i+1) * G i) = (G (i+1) * G i) * E (i+1) := by
    intro i h1 h2
    simp only [hGdef, hEdef]
    rw [← mul_assoc, AuxL_tR P q aff n i (i+1) ⟨h1, by omega⟩ ⟨by omega, h2⟩ (Or.inl rfl),
      AuxL_tL P q aff n (i+1) i ⟨by omega, h2⟩ ⟨h1, by omega⟩ (Or.inr rfl)]
  have c2' : ∀ i, 1 ≤ i → i + 1 < n →
      E (i+1) * (G i * G (i+1)) = (G i * G (i+1)) * E i := by
    intro i h1 h2
    simp only [hGdef, hEdef]
    rw [← mul_assoc, AuxL_tR P q aff n (i+1) i ⟨by omega, h2⟩ ⟨h1, by omega⟩ (Or.inr rfl),
      AuxL_tL P q aff n i (i+1) ⟨h1, by omega⟩ ⟨by omega, h2⟩ (Or.inl rfl)]
  have gX : ∀ i j, 1 ≤ i → i + 2 ≤ j → j < n → G i * G j = G j * G i := fun i j h1 h2 h3 =>
    AuxL_gg P q aff n i j ⟨h1, by omega⟩ ⟨by omega, h3⟩ (Or.inl (by omega))
  have gY : ∀ i j, 1 ≤ j → j + 2 ≤ i → i < n → G i * G j = G j * G i := fun i j h1 h2 h3 =>
    AuxL_gg P q aff n i j ⟨by omega, h3⟩ ⟨h1, by omega⟩ (Or.inr (by omega))
  have eX : ∀ i j, 1 ≤ i → i + 2 ≤ j → j < n → E i * G j = G j * E i := fun i j h1 h2 h3 =>
    (AuxL_ge P q aff n j i ⟨by omega, h3⟩ ⟨h1, by omega⟩ (Or.inr (by omega))).symm
  have eY : ∀ i j, 1 ≤ j → j + 2 ≤ i → i < n → E i * G j = G j * E i := fun i j h1 h2 h3 =>
    (AuxL_ge P q aff n j i ⟨h1, by omega⟩ ⟨by omega, h3⟩ (Or.inl (by omega))).symm
  have bwG := AuxL_bw G G G n gX gY bF
  have fwG := AuxL_fw G G G n gX gY bR
  have bwE := AuxL_bw G E E n eX eY c2
  have fwE := AuxL_fw G E E n eX eY c2'
  refine ⟨?_, c2, ?_, ?_, ?_⟩
  · intro i h1 h2 inv
    cases inv
    · exact bF i h1 h2
    · exact AuxL_conj (AuxL_invR P q aff n i ⟨h1, by omega⟩) (AuxL_invL P q aff n (i+1) ⟨by omega, h2⟩)
        (bF i h1 h2)
  · intro i h1 h2
    have e1 := AuxL_ee P q aff n i (i+2) ⟨h1, by omega⟩ ⟨by omega, h2⟩ (Or.inl (by omega))
    have t1 := AuxL_tL P q aff n i (i+1) ⟨h1, by omega⟩ ⟨by omega, by omega⟩ (Or.inl rfl)
    have t2 := AuxL_tL P q aff n (i+2) (i+1) ⟨by omega, h2⟩ ⟨by omega, by omega⟩ (Or.inr rfl)
    rw [t1]
    calc ghContraction P q aff n (i+1) * ghContraction P q aff n i * ghContraction P q aff n (i+2)
        = ghContraction P q aff n (i+1) * (ghContraction P q aff n (i+2) * ghContraction P q aff n i) := by
          rw [mul_assoc, e1]
      _ = (ghCrossing P q aff n (i+2) false * ghCrossing P q aff n (i+1) false * ghContraction P q aff n (i+2)) *
            ghContraction P q aff n i := by rw [t2, mul_assoc]
      _ = ghCrossing P q aff n (i+2) false * ghCrossing P q aff n (i+1) false *
            (ghContraction P q aff n (i+2) * ghContraction P q aff n i) := by simp only [mul_assoc]
      _ = _ := by rw [← e1, ← mul_assoc]
  · intro i m h1 h2 h3 inv
    cases inv
    · exact ⟨bwG m h3 i h1 h2, fwG m h3 i h1 h2⟩
    · exact ⟨AuxL_conj (AuxL_invR P q aff n i ⟨h1, by omega⟩) (AuxL_invL P q aff n (i+1) ⟨by omega, by omega⟩)
          (bwG m h3 i h1 h2),
        AuxL_conj (AuxL_invR P q aff n (i+1) ⟨by omega, by omega⟩) (AuxL_invL P q aff n i ⟨h1, by omega⟩)
          (fwG m h3 i h1 h2)⟩
  · intro i m h1 h2 h3
    exact ⟨bwE m h3 i h1 h2, fwE m h3 i h1 h2⟩

end QAlgorithms.Papers.Independent.Intake100.P55
