-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P55.proposition_3_12
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T11:46:45.501997+00:00
-- url     : https://prove2.me/submissions/0b3e1a8a-1d72-4868-bf93-27f9301017c9

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55
noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Mon
variable {A : Type*} [Monoid A]

theorem AuxU_bws (h : ℕ → A) (a m : ℕ) : backward h a (m+1) = h (a+m) * backward h a m := by
  simp [backward, List.range_succ]

theorem AuxU_fws (h : ℕ → A) (a m : ℕ) : forward h a (m+1) = forward h a m * h (a+m) := by
  simp [forward, List.range_succ]

theorem AuxU_bwc (h : ℕ → A) (y : A) : ∀ m, (∀ j, 1 ≤ j → j ≤ m → y * h j = h j * y) →
    y * backward h 1 m = backward h 1 m * y := by
  intro m
  induction m with
  | zero => intro _; simp [backward]
  | succ m ih =>
    intro hy
    rw [AuxU_bws]
    have h1 := hy (1+m) (by omega) (by omega)
    have h2 := ih (fun j hj hjm => hy j hj (by omega))
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem AuxU_fwc (h : ℕ → A) (y : A) : ∀ m, (∀ j, 1 ≤ j → j ≤ m → y * h j = h j * y) →
    y * forward h 1 m = forward h 1 m * y := by
  intro m
  induction m with
  | zero => intro _; simp [forward]
  | succ m ih =>
    intro hy
    rw [AuxU_fws]
    have h1 := hy (1+m) (by omega) (by omega)
    have h2 := ih (fun j hj hjm => hy j hj (by omega))
    rw [← mul_assoc, h2, mul_assoc, h1, mul_assoc]

theorem AuxU_bw (h X Y : ℕ → A) (N : ℕ)
    (hX : ∀ i j, 1 ≤ i → i + 2 ≤ j → j < N → X i * h j = h j * X i)
    (hY : ∀ i j, 1 ≤ j → j + 2 ≤ i → i < N → Y i * h j = h j * Y i)
    (hXY : ∀ i, 1 ≤ i → i + 1 < N → X i * (h (i+1) * h i) = (h (i+1) * h i) * Y (i+1)) :
    ∀ m, m < N → ∀ i, 1 ≤ i → i < m → X i * backward h 1 m = backward h 1 m * Y (i+1) := by
  intro m
  induction m with
  | zero => intro _ i _ him; omega
  | succ m ih =>
    intro hm i hi him
    rw [AuxU_bws]
    rcases Nat.lt_or_ge i m with hlt | hge
    · rw [← mul_assoc, hX i (1+m) hi (by omega) (by omega), mul_assoc,
        ih (by omega) i hi hlt, mul_assoc]
    · obtain rfl : i = m := by omega
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      rw [AuxU_bws]
      have e1 : 1 + (k+1) = k + 1 + 1 := by omega
      have e2 : 1 + k = k + 1 := by omega
      rw [e1, e2]
      have hc := AuxU_bwc h (Y (k+1+1)) k (fun j hj hjk => hY (k+1+1) j hj (by omega) (by omega))
      calc X (k+1) * (h (k+1+1) * (h (k+1) * backward h 1 k))
          = X (k+1) * (h (k+1+1) * h (k+1)) * backward h 1 k := by simp only [mul_assoc]
        _ = (h (k+1+1) * h (k+1)) * Y (k+1+1) * backward h 1 k := by
            rw [hXY (k+1) (by omega) (by omega)]
        _ = (h (k+1+1) * h (k+1)) * (backward h 1 k * Y (k+1+1)) := by rw [mul_assoc, hc]
        _ = h (k+1+1) * (h (k+1) * backward h 1 k) * Y (k+1+1) := by simp only [mul_assoc]

theorem AuxU_fw (h X Y : ℕ → A) (N : ℕ)
    (hX : ∀ i j, 1 ≤ i → i + 2 ≤ j → j < N → X i * h j = h j * X i)
    (hY : ∀ i j, 1 ≤ j → j + 2 ≤ i → i < N → Y i * h j = h j * Y i)
    (hYX : ∀ i, 1 ≤ i → i + 1 < N → Y (i+1) * (h i * h (i+1)) = (h i * h (i+1)) * X i) :
    ∀ m, m < N → ∀ i, 1 ≤ i → i < m → Y (i+1) * forward h 1 m = forward h 1 m * X i := by
  intro m
  induction m with
  | zero => intro _ i _ him; omega
  | succ m ih =>
    intro hm i hi him
    rw [AuxU_fws]
    rcases Nat.lt_or_ge i m with hlt | hge
    · rw [← mul_assoc, ih (by omega) i hi hlt, mul_assoc,
        hX i (1+m) hi (by omega) (by omega), mul_assoc]
    · obtain rfl : i = m := by omega
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      rw [AuxU_fws]
      have e1 : 1 + (k+1) = k + 1 + 1 := by omega
      have e2 : 1 + k = k + 1 := by omega
      rw [e1, e2]
      have hc := AuxU_fwc h (Y (k+1+1)) k (fun j hj hjk => hY (k+1+1) j hj (by omega) (by omega))
      calc Y (k+1+1) * (forward h 1 k * h (k+1) * h (k+1+1))
          = (Y (k+1+1) * forward h 1 k) * (h (k+1) * h (k+1+1)) := by simp only [mul_assoc]
        _ = forward h 1 k * (Y (k+1+1) * (h (k+1) * h (k+1+1))) := by rw [hc, mul_assoc]
        _ = forward h 1 k * ((h (k+1) * h (k+1+1)) * X (k+1)) := by
            rw [hYX (k+1) (by omega) (by omega)]
        _ = forward h 1 k * h (k+1) * h (k+1+1) * X (k+1) := by simp only [mul_assoc]

theorem AuxU_conj {a a' b b' c : A} (ha : a' * a = 1) (hb : b * b' = 1) (h : a * c = c * b) :
    a' * c = c * b' := by
  calc a' * c = a' * c * (b * b') := by rw [hb, mul_one]
    _ = a' * (c * b) * b' := by simp only [mul_assoc]
    _ = a' * (a * c) * b' := by rw [h]
    _ = (a' * a) * c * b' := by simp only [mul_assoc]
    _ = c * b' := by rw [ha, one_mul]

end Mon

section Rels
variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R) (aff : Bool) (n : ℕ)

theorem AuxU_invL (i : ℕ) (hi : BMWIndex n i) :
    ghCrossing P q aff n i false * ghCrossing P q aff n i true = 1 := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.invL (P := P) (q := q) (aff := aff) (n := n) i hi)
  simpa only [ghCrossing, presentation, map_mul, map_one] using this

theorem AuxU_invR (i : ℕ) (hi : BMWIndex n i) :
    ghCrossing P q aff n i true * ghCrossing P q aff n i false = 1 := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.invR (P := P) (q := q) (aff := aff) (n := n) i hi)
  simpa only [ghCrossing, presentation, map_mul, map_one] using this

theorem AuxU_braid (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 < n) :
    ghCrossing P q aff n i false * ghCrossing P q aff n (i+1) false * ghCrossing P q aff n i false =
    ghCrossing P q aff n (i+1) false * ghCrossing P q aff n i false * ghCrossing P q aff n (i+1) false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.braid (P := P) (q := q) (aff := aff) (n := n) i h1 h2)
  simpa only [ghCrossing, presentation, map_mul] using this

theorem AuxU_gg (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (hd : i + 1 < j ∨ j + 1 < i) :
    ghCrossing P q aff n i false * ghCrossing P q aff n j false =
    ghCrossing P q aff n j false * ghCrossing P q aff n i false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.ggFar (P := P) (q := q) (aff := aff) (n := n) i j hi hj hd)
  simpa only [ghCrossing, presentation, map_mul] using this

theorem AuxU_ge (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (hd : i + 1 < j ∨ j + 1 < i) :
    ghCrossing P q aff n i false * ghContraction P q aff n j =
    ghContraction P q aff n j * ghCrossing P q aff n i false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.geFar (P := P) (q := q) (aff := aff) (n := n) i j hi hj hd)
  simpa only [ghCrossing, ghContraction, presentation, map_mul] using this

theorem AuxU_ee (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (hd : i + 1 < j ∨ j + 1 < i) :
    ghContraction P q aff n i * ghContraction P q aff n j =
    ghContraction P q aff n j * ghContraction P q aff n i := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.eeFar (P := P) (q := q) (aff := aff) (n := n) i j hi hj hd)
  simpa only [ghContraction, presentation, map_mul] using this

theorem AuxU_tL (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (ha : BMWAdjacent i j) :
    ghCrossing P q aff n i false * ghCrossing P q aff n j false * ghContraction P q aff n i =
    ghContraction P q aff n j * ghContraction P q aff n i := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.tangleL (P := P) (q := q) (aff := aff) (n := n) i j hi hj ha)
  simpa only [ghCrossing, ghContraction, presentation, map_mul] using this

theorem AuxU_tR (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (ha : BMWAdjacent i j) :
    ghContraction P q aff n i * ghCrossing P q aff n j false * ghCrossing P q aff n i false =
    ghContraction P q aff n i * ghContraction P q aff n j := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.tangleR (P := P) (q := q) (aff := aff) (n := n) i j hi hj ha)
  simpa only [ghCrossing, ghContraction, presentation, map_mul] using this

end Rels

theorem AuxU_l39 {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R) (aff : Bool) (n : ℕ) :
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
    rw [← mul_assoc]; exact AuxU_braid P q aff n i h1 h2
  have bR : ∀ i, 1 ≤ i → i + 1 < n →
      G (i+1) * (G i * G (i+1)) = (G i * G (i+1)) * G i := by
    intro i h1 h2
    simp only [hGdef]
    rw [← mul_assoc]; exact (AuxU_braid P q aff n i h1 h2).symm
  have c2 : ∀ i, 1 ≤ i → i + 1 < n →
      E i * (G (i+1) * G i) = (G (i+1) * G i) * E (i+1) := by
    intro i h1 h2
    simp only [hGdef, hEdef]
    rw [← mul_assoc, AuxU_tR P q aff n i (i+1) ⟨h1, by omega⟩ ⟨by omega, h2⟩ (Or.inl rfl),
      AuxU_tL P q aff n (i+1) i ⟨by omega, h2⟩ ⟨h1, by omega⟩ (Or.inr rfl)]
  have c2' : ∀ i, 1 ≤ i → i + 1 < n →
      E (i+1) * (G i * G (i+1)) = (G i * G (i+1)) * E i := by
    intro i h1 h2
    simp only [hGdef, hEdef]
    rw [← mul_assoc, AuxU_tR P q aff n (i+1) i ⟨by omega, h2⟩ ⟨h1, by omega⟩ (Or.inr rfl),
      AuxU_tL P q aff n i (i+1) ⟨h1, by omega⟩ ⟨by omega, h2⟩ (Or.inl rfl)]
  have gX : ∀ i j, 1 ≤ i → i + 2 ≤ j → j < n → G i * G j = G j * G i := fun i j h1 h2 h3 =>
    AuxU_gg P q aff n i j ⟨h1, by omega⟩ ⟨by omega, h3⟩ (Or.inl (by omega))
  have gY : ∀ i j, 1 ≤ j → j + 2 ≤ i → i < n → G i * G j = G j * G i := fun i j h1 h2 h3 =>
    AuxU_gg P q aff n i j ⟨by omega, h3⟩ ⟨h1, by omega⟩ (Or.inr (by omega))
  have eX : ∀ i j, 1 ≤ i → i + 2 ≤ j → j < n → E i * G j = G j * E i := fun i j h1 h2 h3 =>
    (AuxU_ge P q aff n j i ⟨by omega, h3⟩ ⟨h1, by omega⟩ (Or.inr (by omega))).symm
  have eY : ∀ i j, 1 ≤ j → j + 2 ≤ i → i < n → E i * G j = G j * E i := fun i j h1 h2 h3 =>
    (AuxU_ge P q aff n j i ⟨h1, by omega⟩ ⟨by omega, h3⟩ (Or.inl (by omega))).symm
  have bwG := AuxU_bw G G G n gX gY bF
  have fwG := AuxU_fw G G G n gX gY bR
  have bwE := AuxU_bw G E E n eX eY c2
  have fwE := AuxU_fw G E E n eX eY c2'
  refine ⟨?_, c2, ?_, ?_, ?_⟩
  · intro i h1 h2 inv
    cases inv
    · exact bF i h1 h2
    · exact AuxU_conj (AuxU_invR P q aff n i ⟨h1, by omega⟩) (AuxU_invL P q aff n (i+1) ⟨by omega, h2⟩)
        (bF i h1 h2)
  · intro i h1 h2
    have e1 := AuxU_ee P q aff n i (i+2) ⟨h1, by omega⟩ ⟨by omega, h2⟩ (Or.inl (by omega))
    have t1 := AuxU_tL P q aff n i (i+1) ⟨h1, by omega⟩ ⟨by omega, by omega⟩ (Or.inl rfl)
    have t2 := AuxU_tL P q aff n (i+2) (i+1) ⟨by omega, h2⟩ ⟨by omega, by omega⟩ (Or.inr rfl)
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
    · exact ⟨AuxU_conj (AuxU_invR P q aff n i ⟨h1, by omega⟩) (AuxU_invL P q aff n (i+1) ⟨by omega, by omega⟩)
          (bwG m h3 i h1 h2),
        AuxU_conj (AuxU_invR P q aff n (i+1) ⟨by omega, by omega⟩) (AuxU_invL P q aff n i ⟨h1, by omega⟩)
          (fwG m h3 i h1 h2)⟩
  · intro i m h1 h2 h3
    exact ⟨bwE m h3 i h1 h2, fwE m h3 i h1 h2⟩


section Aff
variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R) (n : ℕ)

theorem AuxU_xg (j : ℕ) (hj : 2 ≤ j) (hjn : j < n) :
    bmwX P q true n false * ghCrossing P q true n j false = ghCrossing P q true n j false * bmwX P q true n false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.xgFar (P := P) (q := q) (aff := true) (n := n) rfl j hj hjn)
  simpa only [ghCrossing, bmwX, presentation, map_mul] using this

theorem AuxU_xe (j : ℕ) (hj : 2 ≤ j) (hjn : j < n) :
    bmwX P q true n false * ghContraction P q true n j = ghContraction P q true n j * bmwX P q true n false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.xeFar (P := P) (q := q) (aff := true) (n := n) rfl j hj hjn)
  simpa only [ghContraction, bmwX, presentation, map_mul] using this

theorem AuxU_ab (hn : 2 ≤ n) :
    bmwX P q true n false * ghCrossing P q true n 1 false * bmwX P q true n false * ghCrossing P q true n 1 false =
    ghCrossing P q true n 1 false * bmwX P q true n false * ghCrossing P q true n 1 false * bmwX P q true n false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.affineBraid (P := P) (q := q) (aff := true) (n := n) rfl hn)
  simpa only [ghCrossing, bmwX, presentation, map_mul] using this

theorem AuxU_def (r : ℕ) (hr : 1 ≤ r) : bmwWinding P q n false r =
    backward (fun j => ghCrossing P q true n j false) 1 (r-1) * bmwX P q true n false *
      forward (fun j => ghCrossing P q true n j false) 1 (r-1) := by
  rw [bmwWinding, if_neg (by omega)]

theorem AuxU_one : bmwWinding P q n false 1 = bmwX P q true n false := by
  rw [AuxU_def P q n 1 le_rfl]; simp [backward, forward]

theorem AuxU_succ (r : ℕ) (hr : 1 ≤ r) : bmwWinding P q n false (r+1) =
    ghCrossing P q true n r false * bmwWinding P q n false r * ghCrossing P q true n r false := by
  rw [AuxU_def P q n (r+1) (by omega), AuxU_def P q n r hr]
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have e1 : s + 1 + 1 - 1 = s + 1 := by omega
  have e2 : s + 1 - 1 = s := by omega
  rw [e1, e2, AuxU_bws, AuxU_fws]
  have e3 : 1 + s = s + 1 := by omega
  rw [e3]; simp only [mul_assoc]

theorem AuxU_C1 (r j : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ n) (hj : BMWIndex n j) (hne1 : j ≠ r) (hne2 : j + 1 ≠ r) :
    ghCrossing P q true n j false * bmwWinding P q n false r =
      bmwWinding P q n false r * ghCrossing P q true n j false := by
  rw [AuxU_def P q n r h1]
  have L := AuxU_l39 P q true n
  have hj1 := hj.1
  have hj2 := hj.2
  rcases (show r + 1 ≤ j ∨ j + 2 ≤ r by omega) with hf | hc
  · have cB := AuxU_bwc (fun j => ghCrossing P q true n j false) (ghCrossing P q true n j false) (r-1)
      (fun i hi1 hi2 => AuxU_gg P q true n j i hj ⟨hi1, by omega⟩ (Or.inr (by omega)))
    have cF := AuxU_fwc (fun j => ghCrossing P q true n j false) (ghCrossing P q true n j false) (r-1)
      (fun i hi1 hi2 => AuxU_gg P q true n j i hj ⟨hi1, by omega⟩ (Or.inr (by omega)))
    have cX := (AuxU_xg P q n j (by omega) hj.2).symm
    exact (Commute.mul_right (Commute.mul_right cB cX) cF).eq
  · have hb := (L.2.2.2.1 j (r-1) hj.1 (by omega) (by omega) false).1
    have hf := (L.2.2.2.1 j (r-1) hj.1 (by omega) (by omega) false).2
    have cX := (AuxU_xg P q n (j+1) (by omega) (by omega)).symm
    calc ghCrossing P q true n j false * (backward (fun j => ghCrossing P q true n j false) 1 (r-1) *
          bmwX P q true n false * forward (fun j => ghCrossing P q true n j false) 1 (r-1))
        = (ghCrossing P q true n j false * backward (fun j => ghCrossing P q true n j false) 1 (r-1)) *
          bmwX P q true n false * forward (fun j => ghCrossing P q true n j false) 1 (r-1) := by
            simp only [mul_assoc]
      _ = backward (fun j => ghCrossing P q true n j false) 1 (r-1) *
          (ghCrossing P q true n (j+1) false * bmwX P q true n false) *
          forward (fun j => ghCrossing P q true n j false) 1 (r-1) := by rw [hb]; simp only [mul_assoc]
      _ = backward (fun j => ghCrossing P q true n j false) 1 (r-1) * bmwX P q true n false *
          (ghCrossing P q true n (j+1) false * forward (fun j => ghCrossing P q true n j false) 1 (r-1)) := by
            rw [cX]; simp only [mul_assoc]
      _ = _ := by rw [hf]; simp only [mul_assoc]

theorem AuxU_C2 (r j : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ n) (hj : BMWIndex n j) (hne1 : j ≠ r) (hne2 : j + 1 ≠ r) :
    ghContraction P q true n j * bmwWinding P q n false r =
      bmwWinding P q n false r * ghContraction P q true n j := by
  rw [AuxU_def P q n r h1]
  have L := AuxU_l39 P q true n
  have hj1 := hj.1
  have hj2 := hj.2
  rcases (show r + 1 ≤ j ∨ j + 2 ≤ r by omega) with hf | hc
  · have cB := AuxU_bwc (fun j => ghCrossing P q true n j false) (ghContraction P q true n j) (r-1)
      (fun i hi1 hi2 => (AuxU_ge P q true n i j ⟨hi1, by omega⟩ hj (Or.inl (by omega))).symm)
    have cF := AuxU_fwc (fun j => ghCrossing P q true n j false) (ghContraction P q true n j) (r-1)
      (fun i hi1 hi2 => (AuxU_ge P q true n i j ⟨hi1, by omega⟩ hj (Or.inl (by omega))).symm)
    have cX := (AuxU_xe P q n j (by omega) hj.2).symm
    exact (Commute.mul_right (Commute.mul_right cB cX) cF).eq
  · have hb := (L.2.2.2.2 j (r-1) hj.1 (by omega) (by omega)).1
    have hf := (L.2.2.2.2 j (r-1) hj.1 (by omega) (by omega)).2
    have cX := (AuxU_xe P q n (j+1) (by omega) (by omega)).symm
    calc ghContraction P q true n j * (backward (fun j => ghCrossing P q true n j false) 1 (r-1) *
          bmwX P q true n false * forward (fun j => ghCrossing P q true n j false) 1 (r-1))
        = (ghContraction P q true n j * backward (fun j => ghCrossing P q true n j false) 1 (r-1)) *
          bmwX P q true n false * forward (fun j => ghCrossing P q true n j false) 1 (r-1) := by
            simp only [mul_assoc]
      _ = backward (fun j => ghCrossing P q true n j false) 1 (r-1) *
          (ghContraction P q true n (j+1) * bmwX P q true n false) *
          forward (fun j => ghCrossing P q true n j false) 1 (r-1) := by rw [hb]; simp only [mul_assoc]
      _ = backward (fun j => ghCrossing P q true n j false) 1 (r-1) * bmwX P q true n false *
          (ghContraction P q true n (j+1) * forward (fun j => ghCrossing P q true n j false) 1 (r-1)) := by
            rw [cX]; simp only [mul_assoc]
      _ = _ := by rw [hf]; simp only [mul_assoc]

end Aff

theorem AuxU_mon {A : Type*} [Monoid A] {a b x : A} (hb : a*b*a = b*a*b) (hxb : x*b = b*x)
    (ih : x*a*x*a = a*x*a*x) : (a*x*a)*(b*(a*x*a)*b) = (b*(a*x*a)*b)*(a*x*a) := by
  calc (a*x*a)*(b*(a*x*a)*b) = a*x*(a*b*a)*x*a*b := by simp only [mul_assoc]
    _ = a*x*(b*a*b)*x*a*b := by rw [hb]
    _ = a*(x*b)*a*(b*x)*a*b := by simp only [mul_assoc]
    _ = a*(b*x)*a*(x*b)*a*b := by rw [hxb]
    _ = a*b*(x*a*x)*(b*a*b) := by simp only [mul_assoc]
    _ = a*b*(x*a*x)*(a*b*a) := by rw [hb]
    _ = a*b*(x*a*x*a)*b*a := by simp only [mul_assoc]
    _ = a*b*(a*x*a*x)*b*a := by rw [ih]
    _ = (a*b*a)*(x*a*x)*b*a := by simp only [mul_assoc]
    _ = (b*a*b)*(x*a*x)*b*a := by rw [hb]
    _ = b*a*(b*x)*a*(x*b)*a := by simp only [mul_assoc]
    _ = b*a*(x*b)*a*(b*x)*a := by rw [hxb]
    _ = b*a*x*(b*a*b)*x*a := by simp only [mul_assoc]
    _ = b*a*x*(a*b*a)*x*a := by rw [hb]
    _ = (b*(a*x*a)*b)*(a*x*a) := by simp only [mul_assoc]

section Aff2
variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R) (n : ℕ)

theorem AuxU_adj (r : ℕ) (hr : 1 ≤ r) : r + 1 ≤ n →
    bmwWinding P q n false r * bmwWinding P q n false (r+1) =
      bmwWinding P q n false (r+1) * bmwWinding P q n false r := by
  induction r, hr using Nat.le_induction with
  | base =>
    intro hn
    rw [AuxU_succ P q n 1 le_rfl, AuxU_one]
    have := AuxU_ab P q n hn
    simp only [mul_assoc] at this ⊢
    exact this
  | succ s hs ih =>
    intro hn
    have ih' := ih (by omega)
    rw [AuxU_succ P q n (s+1) (by omega), AuxU_succ P q n s hs]
    rw [AuxU_succ P q n s hs] at ih'
    apply AuxU_mon
    · exact AuxU_braid P q true n s hs (by omega)
    · exact (AuxU_C1 P q n s (s+1) hs (by omega) ⟨by omega, by omega⟩ (by omega) (by omega)).symm
    · simp only [mul_assoc] at ih' ⊢; exact ih'

theorem AuxU_far (d : ℕ) : ∀ j, 1 ≤ j → j + d + 1 ≤ n →
    Commute (bmwWinding P q n false j) (bmwWinding P q n false (j+d+1)) := by
  induction d with
  | zero => intro j hj hn; exact AuxU_adj P q n j hj (by omega)
  | succ d ih =>
    intro j hj hn
    have e : j + (d+1) + 1 = (j+d+1) + 1 := by omega
    rw [e, AuxU_succ P q n (j+d+1) (by omega)]
    have cg : Commute (bmwWinding P q n false j) (ghCrossing P q true n (j+d+1) false) :=
      (AuxU_C1 P q n j (j+d+1) hj (by omega) ⟨by omega, by omega⟩ (by omega) (by omega)).symm
    exact (cg.mul_right (ih j hj (by omega))).mul_right cg

theorem AuxU_310 {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R) (n : ℕ) :
    (∀ r j, 1 ≤ r → r ≤ n → BMWIndex n j → j ≠ r → j+1 ≠ r →
      ghCrossing P q true n j false * bmwWinding P q n false r =
        bmwWinding P q n false r * ghCrossing P q true n j false) ∧
    (∀ r j, 1 ≤ r → r ≤ n → BMWIndex n j → j ≠ r → j+1 ≠ r →
      ghContraction P q true n j * bmwWinding P q n false r =
        bmwWinding P q n false r * ghContraction P q true n j) ∧
    (∀ r j, 1 ≤ r → r ≤ n → 1 ≤ j → j ≤ n →
      bmwWinding P q n false j * bmwWinding P q n false r =
        bmwWinding P q n false r * bmwWinding P q n false j) := by
  refine ⟨fun r j h1 h2 hj a b => AuxU_C1 P q n r j h1 h2 hj a b,
    fun r j h1 h2 hj a b => AuxU_C2 P q n r j h1 h2 hj a b, ?_⟩
  intro r j h1 h2 h3 h4
  rcases lt_trichotomy j r with h | h | h
  · obtain ⟨d, rfl⟩ : ∃ d, r = j + d + 1 := ⟨r - j - 1, by omega⟩
    exact (AuxU_far P q n d j h3 h2).eq
  · subst h; rfl
  · obtain ⟨d, rfl⟩ : ∃ d, j = r + d + 1 := ⟨j - r - 1, by omega⟩
    exact (AuxU_far P q n d r h1 h4).eq.symm

end Aff2


section Mon2
variable {A : Type*} [Monoid A]

theorem AuxU_tel1 (h h' : ℕ → A) : ∀ m, (∀ i, 1 ≤ i → i ≤ m → h i * h' i = 1) →
    forward h 1 m * backward h' 1 m = 1 := by
  intro m
  induction m with
  | zero => intro _; simp [forward, backward]
  | succ m ih =>
    intro hh
    rw [AuxU_fws, AuxU_bws, mul_assoc, ← mul_assoc (h (1+m)), hh (1+m) (by omega) (by omega), one_mul,
      ih (fun i h1 h2 => hh i h1 (by omega))]

theorem AuxU_tel2 (h h' : ℕ → A) : ∀ m, (∀ i, 1 ≤ i → i ≤ m → h i * h' i = 1) →
    backward h 1 m * forward h' 1 m = 1 := by
  intro m
  induction m with
  | zero => intro _; simp [forward, backward]
  | succ m ih =>
    intro hh
    rw [AuxU_fws, AuxU_bws, mul_assoc, ← mul_assoc (backward h 1 m),
      ih (fun i h1 h2 => hh i h1 (by omega)), one_mul, hh (1+m) (by omega) (by omega)]

end Mon2

section Alg2
variable {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A]

theorem AuxU_ustep {a b x e e' : A} (c l : R) (hcl : c * (c * l) = c)
    (hb : a*b*a = b*a*b) (hxb : x*b = b*x) (htR : e*a*b = e*e') (ih : e'*x*a*x = c • e')
    (hc2 : e'*(b*a) = (b*a)*e) (hun : e*b = c • e) (hnear : e*a*e = l • e) :
    e*(a*x*a)*b*(a*x*a) = c • e := by
  calc e*(a*x*a)*b*(a*x*a) = e*a*x*(a*b*a)*x*a := by simp only [mul_assoc]
    _ = e*a*x*(b*a*b)*x*a := by rw [hb]
    _ = e*a*(x*b)*a*(b*x)*a := by simp only [mul_assoc]
    _ = e*a*(b*x)*a*(x*b)*a := by rw [hxb]
    _ = (e*a*b)*(x*a*x)*b*a := by simp only [mul_assoc]
    _ = (e*e')*(x*a*x)*b*a := by rw [htR]
    _ = e*(e'*x*a*x)*b*a := by simp only [mul_assoc]
    _ = e*(c • e')*b*a := by rw [ih]
    _ = c • (e*(e'*(b*a))) := by simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = c • (e*((b*a)*e)) := by rw [hc2]
    _ = c • ((e*b)*a*e) := by simp only [mul_assoc]
    _ = c • ((c • e)*a*e) := by rw [hun]
    _ = c • c • (e*a*e) := by simp only [smul_mul_assoc, mul_assoc]
    _ = c • c • (l • e) := by rw [hnear]
    _ = (c * (c * l)) • e := by simp only [smul_smul]
    _ = c • e := by rw [hcl]

theorem AuxU_c3 {e x g gi : A} (c : R) (t : ℕ) (hK : g*x*g*x = x*g*x*g) (hU : e*x*g*x = c • e)
    (hun : e*g = c • e) (hg : g*gi = 1) : e * x^(t+1) * g * x = (c*c) • (e * x^t * gi) := by
  have cx : Commute x (x*g*x*g) := by
    show x*(x*g*x*g) = (x*g*x*g)*x
    calc x*(x*g*x*g) = x*(g*x*g*x) := by rw [hK]
      _ = (x*g*x*g)*x := by simp only [mul_assoc]
  have cxt := cx.pow_left t
  calc e * x^(t+1) * g * x = e * x^t * (x*g*x*g) * gi := by
        rw [pow_succ]; simp only [mul_assoc]; rw [hg, mul_one]
    _ = e * (x*g*x*g) * x^t * gi := by
        rw [show e * x^t * (x*g*x*g) * gi = e * (x^t * (x*g*x*g)) * gi by simp only [mul_assoc], cxt.eq]
        simp only [mul_assoc]
    _ = (e*x*g*x)*g*x^t*gi := by simp only [mul_assoc]
    _ = (c • e)*g*x^t*gi := by rw [hU]
    _ = c • ((e*g)*x^t*gi) := by simp only [smul_mul_assoc, mul_assoc]
    _ = c • ((c • e)*x^t*gi) := by rw [hun]
    _ = (c*c) • (e*x^t*gi) := by simp only [smul_mul_assoc, smul_smul, mul_assoc]

theorem AuxU_c4 {e x g gi xi : A} (c l : R) (t : ℕ) (hlc : l * c = 1) (hK : g*x*g*x = x*g*x*g)
    (hU : e*x*g*x = c • e) (hun : e*g = c • e) (hggi : g*gi = 1) (hgig : gi*g = 1)
    (hxxi : x*xi = 1) (hxix : xi*x = 1) :
    e * xi^(t+1) * gi * xi = (l*l) • (e * xi^t * g) := by
  have a1 : ∀ y : A, g*(gi*y) = y := fun y => by rw [← mul_assoc, hggi, one_mul]
  have a2 : ∀ y : A, gi*(g*y) = y := fun y => by rw [← mul_assoc, hgig, one_mul]
  have a3 : ∀ y : A, x*(xi*y) = y := fun y => by rw [← mul_assoc, hxxi, one_mul]
  have a4 : ∀ y : A, xi*(x*y) = y := fun y => by rw [← mul_assoc, hxix, one_mul]
  have h1 : (x*g*x)*(xi*gi*xi) = 1 := by simp only [mul_assoc, a1, a2, a3, a4, hxxi, hggi]
  have hU' : e*xi*gi*xi = l • e := by
    calc e*xi*gi*xi = (l*c) • (e*xi*gi*xi) := by rw [hlc, one_smul]
      _ = l • ((c • e)*(xi*gi*xi)) := by rw [smul_mul_assoc, smul_smul]; simp only [mul_assoc]
      _ = l • ((e*x*g*x)*(xi*gi*xi)) := by rw [hU]
      _ = l • (e * ((x*g*x)*(xi*gi*xi))) := by simp only [mul_assoc]
      _ = l • e := by rw [h1, mul_one]
  have hun' : e*gi = l • e := by
    calc e*gi = (l*c) • (e*gi) := by rw [hlc, one_smul]
      _ = l • ((c • e)*gi) := by rw [smul_mul_assoc, smul_smul]
      _ = l • ((e*g)*gi) := by rw [hun]
      _ = l • e := by rw [mul_assoc, hggi, mul_one]
  have hK' : gi*xi*gi*xi = xi*gi*xi*gi := by
    calc gi*xi*gi*xi = ((xi*gi*xi*gi) * (g*x*g*x)) * (gi*xi*gi*xi) := by
          simp only [mul_assoc, a1, a2, a3, a4, hxxi, hggi, hxix, hgig, mul_one, one_mul]
      _ = (xi*gi*xi*gi) * (x*g*x*g) * (gi*xi*gi*xi) := by rw [hK]
      _ = xi*gi*xi*gi := by simp only [mul_assoc, a1, a2, a3, a4, hxxi, hggi, hxix, hgig, mul_one, one_mul]
  exact AuxU_c3 l t hK' hU' hun' hgig

end Alg2

section Aff3
variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R) (N : ℕ)

theorem AuxU_xinvL (hn : 1 ≤ N) : bmwX P q true N false * bmwX P q true N true = 1 := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.xInvL (P := P) (q := q) (aff := true) (n := N) rfl hn)
  simpa only [bmwX, presentation, map_mul, map_one] using this

theorem AuxU_xinvR (hn : 1 ≤ N) : bmwX P q true N true * bmwX P q true N false = 1 := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.xInvR (P := P) (q := q) (aff := true) (n := N) rfl hn)
  simpa only [bmwX, presentation, map_mul, map_one] using this

theorem AuxU_unwrap (hn : 2 ≤ N) : ghContraction P q true N 1 * bmwX P q true N false *
    ghCrossing P q true N 1 false * bmwX P q true N false = (↑P.lam⁻¹ : R) • ghContraction P q true N 1 := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.unwrapL (P := P) (q := q) (aff := true) (n := N) rfl hn)
  rw [Algebra.smul_def]
  simpa only [ghCrossing, ghContraction, bmwX, presentation, map_mul, AlgHom.commutes] using this

theorem AuxU_untR (i : ℕ) (hi : BMWIndex N i) : ghContraction P q true N i * ghCrossing P q true N i false =
    (↑P.lam⁻¹ : R) • ghContraction P q true N i := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.untwistR (P := P) (q := q) (aff := true) (n := N) i hi)
  rw [Algebra.smul_def]
  simpa only [ghCrossing, ghContraction, presentation, map_mul, AlgHom.commutes] using this

theorem AuxU_near (i j : ℕ) (hi : BMWIndex N i) (hj : BMWIndex N j) (ha : BMWAdjacent i j) :
    ghContraction P q true N i * ghCrossing P q true N j false * ghContraction P q true N i =
    (P.lam : R) • ghContraction P q true N i := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.untwistNear (P := P) (q := q) (aff := true) (n := N) i j hi hj ha)
  rw [Algebra.smul_def]
  simpa only [ghCrossing, ghContraction, presentation, map_mul, AlgHom.commutes] using this

theorem AuxU_defi (r : ℕ) (hr : 1 ≤ r) : bmwWinding P q N true r =
    backward (fun j => ghCrossing P q true N j true) 1 (r-1) * bmwX P q true N true *
      forward (fun j => ghCrossing P q true N j true) 1 (r-1) := by
  rw [bmwWinding, if_neg (by omega)]

theorem AuxU_U : ∀ r, 1 ≤ r → r < N →
    ghContraction P q true N r * bmwWinding P q N false r * ghCrossing P q true N r false *
      bmwWinding P q N false r = (↑P.lam⁻¹ : R) • ghContraction P q true N r := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    intro hN
    rw [AuxU_one]
    exact AuxU_unwrap P q N hN
  | succ s hs ih =>
    intro hN
    rw [AuxU_succ P q N s hs]
    have hcl : (↑P.lam⁻¹ : R) * ((↑P.lam⁻¹ : R) * (P.lam : R)) = (↑P.lam⁻¹ : R) := by
      rw [Units.inv_mul, mul_one]
    refine AuxU_ustep (↑P.lam⁻¹ : R) (P.lam : R) hcl
      (AuxU_braid P q true N s hs hN)
      (AuxU_C1 P q N s (s+1) hs (by omega) ⟨by omega, hN⟩ (by omega) (by omega)).symm
      (AuxU_tR P q true N (s+1) s ⟨by omega, hN⟩ ⟨hs, by omega⟩ (Or.inr rfl))
      (ih (by omega))
      ((AuxU_l39 P q true N).2.1 s hs hN)
      (AuxU_untR P q N (s+1) ⟨by omega, hN⟩)
      (AuxU_near P q N (s+1) s ⟨by omega, hN⟩ ⟨hs, by omega⟩ (Or.inr rfl))

theorem AuxU_xxi (r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N) :
    bmwWinding P q N false r * bmwWinding P q N true r = 1 ∧
    bmwWinding P q N true r * bmwWinding P q N false r = 1 := by
  rw [AuxU_def P q N r hr, AuxU_defi P q N r hr]
  have i1 : ∀ i, 1 ≤ i → i ≤ r - 1 → ghCrossing P q true N i false * ghCrossing P q true N i true = 1 :=
    fun i h1 h2 => AuxU_invL P q true N i ⟨h1, by omega⟩
  have i2 : ∀ i, 1 ≤ i → i ≤ r - 1 → ghCrossing P q true N i true * ghCrossing P q true N i false = 1 :=
    fun i h1 h2 => AuxU_invR P q true N i ⟨h1, by omega⟩
  have t1 := AuxU_tel1 (fun j => ghCrossing P q true N j false) (fun j => ghCrossing P q true N j true) (r-1) i1
  have t2 := AuxU_tel2 (fun j => ghCrossing P q true N j false) (fun j => ghCrossing P q true N j true) (r-1) i1
  have t3 := AuxU_tel1 (fun j => ghCrossing P q true N j true) (fun j => ghCrossing P q true N j false) (r-1) i2
  have t4 := AuxU_tel2 (fun j => ghCrossing P q true N j true) (fun j => ghCrossing P q true N j false) (r-1) i2
  have x1 := AuxU_xinvL P q N (by omega)
  have x2 := AuxU_xinvR P q N (by omega)
  constructor
  · calc _ = backward (fun j => ghCrossing P q true N j false) 1 (r-1) * bmwX P q true N false *
            (forward (fun j => ghCrossing P q true N j false) 1 (r-1) *
              backward (fun j => ghCrossing P q true N j true) 1 (r-1)) * bmwX P q true N true *
            forward (fun j => ghCrossing P q true N j true) 1 (r-1) := by simp only [mul_assoc]
      _ = backward (fun j => ghCrossing P q true N j false) 1 (r-1) *
            (bmwX P q true N false * bmwX P q true N true) *
            forward (fun j => ghCrossing P q true N j true) 1 (r-1) := by rw [t1, mul_one]; simp only [mul_assoc]
      _ = 1 := by rw [x1, mul_one, t2]
  · calc _ = backward (fun j => ghCrossing P q true N j true) 1 (r-1) * bmwX P q true N true *
            (forward (fun j => ghCrossing P q true N j true) 1 (r-1) *
              backward (fun j => ghCrossing P q true N j false) 1 (r-1)) * bmwX P q true N false *
            forward (fun j => ghCrossing P q true N j false) 1 (r-1) := by simp only [mul_assoc]
      _ = backward (fun j => ghCrossing P q true N j true) 1 (r-1) *
            (bmwX P q true N true * bmwX P q true N false) *
            forward (fun j => ghCrossing P q true N j false) 1 (r-1) := by rw [t3, mul_one]; simp only [mul_assoc]
      _ = 1 := by rw [x2, mul_one, t4]

theorem AuxU_main (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    ghCrossing P q true (n+1) n false * bmwWinding P q (n+1) false n * ghCrossing P q true (n+1) n false *
      bmwWinding P q (n+1) false n =
    bmwWinding P q (n+1) false n * ghCrossing P q true (n+1) n false * bmwWinding P q (n+1) false n *
      ghCrossing P q true (n+1) n false ∧
    ghContraction P q true (n+1) n * bmwWinding P q (n+1) false n * ghCrossing P q true (n+1) n false *
      bmwWinding P q (n+1) false n = algebraMap R _ (↑P.lam⁻¹ : R) * ghContraction P q true (n+1) n ∧
    ghContraction P q true (n+1) n * bmwWinding P q (n+1) false n ^ r * ghCrossing P q true (n+1) n false *
      bmwWinding P q (n+1) false n = algebraMap R _ ((↑P.lam⁻¹ : R)^2) * ghContraction P q true (n+1) n *
      bmwWinding P q (n+1) false n ^ (r-1) * ghCrossing P q true (n+1) n true ∧
    ghContraction P q true (n+1) n * bmwWinding P q (n+1) true n ^ r * ghCrossing P q true (n+1) n true *
      bmwWinding P q (n+1) true n = algebraMap R _ ((P.lam : R)^2) * ghContraction P q true (n+1) n *
      bmwWinding P q (n+1) true n ^ (r-1) * ghCrossing P q true (n+1) n false := by
  have hK : ghCrossing P q true (n+1) n false * bmwWinding P q (n+1) false n * ghCrossing P q true (n+1) n false *
      bmwWinding P q (n+1) false n =
    bmwWinding P q (n+1) false n * ghCrossing P q true (n+1) n false * bmwWinding P q (n+1) false n *
      ghCrossing P q true (n+1) n false := by
    have := AuxU_adj P q (n+1) n hn le_rfl
    rw [AuxU_succ P q (n+1) n hn] at this
    simp only [mul_assoc] at this ⊢
    exact this.symm
  have hU := AuxU_U P q (n+1) n hn (by omega)
  have hun := AuxU_untR P q (n+1) n ⟨hn, by omega⟩
  have hggi := AuxU_invL P q true (n+1) n ⟨hn, by omega⟩
  have hgig := AuxU_invR P q true (n+1) n ⟨hn, by omega⟩
  obtain ⟨hxxi, hxix⟩ := AuxU_xxi P q (n+1) n hn (by omega)
  have hlc : (P.lam : R) * (↑P.lam⁻¹ : R) = 1 := Units.mul_inv _
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
  have et : t + 1 - 1 = t := by omega
  rw [et]
  refine ⟨hK, by rw [hU, Algebra.smul_def], ?_, ?_⟩
  · rw [AuxU_c3 _ t hK hU hun hggi, Algebra.smul_def, ← sq]; simp only [mul_assoc]
  · rw [AuxU_c4 _ _ t hlc hK hU hun hggi hgig hxxi hxix, Algebra.smul_def, ← sq]; simp only [mul_assoc]

end Aff3

theorem _root_.solution {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R) (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    let g := ghCrossing P q true (n+1) n false
    let gi := ghCrossing P q true (n+1) n true
    let e := ghContraction P q true (n+1) n
    let x := bmwWinding P q (n+1) false n
    let xi := bmwWinding P q (n+1) true n
    g*x*g*x = x*g*x*g ∧
    e*x*g*x = algebraMap R _ (↑P.lam⁻¹ : R)*e ∧
    e*x^r*g*x = algebraMap R _ ((↑P.lam⁻¹ : R)^2)*e*x^(r-1)*gi ∧
    e*xi^r*gi*xi = algebraMap R _ ((P.lam : R)^2)*e*xi^(r-1)*g := by
  intro g gi e x xi
  exact AuxU_main P q n r hn hr

end QAlgorithms.Papers.Independent.Intake100.P55
