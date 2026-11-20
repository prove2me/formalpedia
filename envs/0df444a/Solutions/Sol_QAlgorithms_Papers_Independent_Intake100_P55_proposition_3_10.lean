-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P55.proposition_3_10
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T11:42:05.458614+00:00
-- url     : https://prove2.me/submissions/2c2fd3c5-bb02-482f-8489-b6276e8f40c7

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55
noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Mon
variable {A : Type*} [Monoid A]

theorem AuxW_bws (h : ℕ → A) (a m : ℕ) : backward h a (m+1) = h (a+m) * backward h a m := by
  simp [backward, List.range_succ]

theorem AuxW_fws (h : ℕ → A) (a m : ℕ) : forward h a (m+1) = forward h a m * h (a+m) := by
  simp [forward, List.range_succ]

theorem AuxW_bwc (h : ℕ → A) (y : A) : ∀ m, (∀ j, 1 ≤ j → j ≤ m → y * h j = h j * y) →
    y * backward h 1 m = backward h 1 m * y := by
  intro m
  induction m with
  | zero => intro _; simp [backward]
  | succ m ih =>
    intro hy
    rw [AuxW_bws]
    have h1 := hy (1+m) (by omega) (by omega)
    have h2 := ih (fun j hj hjm => hy j hj (by omega))
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem AuxW_fwc (h : ℕ → A) (y : A) : ∀ m, (∀ j, 1 ≤ j → j ≤ m → y * h j = h j * y) →
    y * forward h 1 m = forward h 1 m * y := by
  intro m
  induction m with
  | zero => intro _; simp [forward]
  | succ m ih =>
    intro hy
    rw [AuxW_fws]
    have h1 := hy (1+m) (by omega) (by omega)
    have h2 := ih (fun j hj hjm => hy j hj (by omega))
    rw [← mul_assoc, h2, mul_assoc, h1, mul_assoc]

theorem AuxW_bw (h X Y : ℕ → A) (N : ℕ)
    (hX : ∀ i j, 1 ≤ i → i + 2 ≤ j → j < N → X i * h j = h j * X i)
    (hY : ∀ i j, 1 ≤ j → j + 2 ≤ i → i < N → Y i * h j = h j * Y i)
    (hXY : ∀ i, 1 ≤ i → i + 1 < N → X i * (h (i+1) * h i) = (h (i+1) * h i) * Y (i+1)) :
    ∀ m, m < N → ∀ i, 1 ≤ i → i < m → X i * backward h 1 m = backward h 1 m * Y (i+1) := by
  intro m
  induction m with
  | zero => intro _ i _ him; omega
  | succ m ih =>
    intro hm i hi him
    rw [AuxW_bws]
    rcases Nat.lt_or_ge i m with hlt | hge
    · rw [← mul_assoc, hX i (1+m) hi (by omega) (by omega), mul_assoc,
        ih (by omega) i hi hlt, mul_assoc]
    · obtain rfl : i = m := by omega
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      rw [AuxW_bws]
      have e1 : 1 + (k+1) = k + 1 + 1 := by omega
      have e2 : 1 + k = k + 1 := by omega
      rw [e1, e2]
      have hc := AuxW_bwc h (Y (k+1+1)) k (fun j hj hjk => hY (k+1+1) j hj (by omega) (by omega))
      calc X (k+1) * (h (k+1+1) * (h (k+1) * backward h 1 k))
          = X (k+1) * (h (k+1+1) * h (k+1)) * backward h 1 k := by simp only [mul_assoc]
        _ = (h (k+1+1) * h (k+1)) * Y (k+1+1) * backward h 1 k := by
            rw [hXY (k+1) (by omega) (by omega)]
        _ = (h (k+1+1) * h (k+1)) * (backward h 1 k * Y (k+1+1)) := by rw [mul_assoc, hc]
        _ = h (k+1+1) * (h (k+1) * backward h 1 k) * Y (k+1+1) := by simp only [mul_assoc]

theorem AuxW_fw (h X Y : ℕ → A) (N : ℕ)
    (hX : ∀ i j, 1 ≤ i → i + 2 ≤ j → j < N → X i * h j = h j * X i)
    (hY : ∀ i j, 1 ≤ j → j + 2 ≤ i → i < N → Y i * h j = h j * Y i)
    (hYX : ∀ i, 1 ≤ i → i + 1 < N → Y (i+1) * (h i * h (i+1)) = (h i * h (i+1)) * X i) :
    ∀ m, m < N → ∀ i, 1 ≤ i → i < m → Y (i+1) * forward h 1 m = forward h 1 m * X i := by
  intro m
  induction m with
  | zero => intro _ i _ him; omega
  | succ m ih =>
    intro hm i hi him
    rw [AuxW_fws]
    rcases Nat.lt_or_ge i m with hlt | hge
    · rw [← mul_assoc, ih (by omega) i hi hlt, mul_assoc,
        hX i (1+m) hi (by omega) (by omega), mul_assoc]
    · obtain rfl : i = m := by omega
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      rw [AuxW_fws]
      have e1 : 1 + (k+1) = k + 1 + 1 := by omega
      have e2 : 1 + k = k + 1 := by omega
      rw [e1, e2]
      have hc := AuxW_fwc h (Y (k+1+1)) k (fun j hj hjk => hY (k+1+1) j hj (by omega) (by omega))
      calc Y (k+1+1) * (forward h 1 k * h (k+1) * h (k+1+1))
          = (Y (k+1+1) * forward h 1 k) * (h (k+1) * h (k+1+1)) := by simp only [mul_assoc]
        _ = forward h 1 k * (Y (k+1+1) * (h (k+1) * h (k+1+1))) := by rw [hc, mul_assoc]
        _ = forward h 1 k * ((h (k+1) * h (k+1+1)) * X (k+1)) := by
            rw [hYX (k+1) (by omega) (by omega)]
        _ = forward h 1 k * h (k+1) * h (k+1+1) * X (k+1) := by simp only [mul_assoc]

theorem AuxW_conj {a a' b b' c : A} (ha : a' * a = 1) (hb : b * b' = 1) (h : a * c = c * b) :
    a' * c = c * b' := by
  calc a' * c = a' * c * (b * b') := by rw [hb, mul_one]
    _ = a' * (c * b) * b' := by simp only [mul_assoc]
    _ = a' * (a * c) * b' := by rw [h]
    _ = (a' * a) * c * b' := by simp only [mul_assoc]
    _ = c * b' := by rw [ha, one_mul]

end Mon

section Rels
variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R) (aff : Bool) (n : ℕ)

theorem AuxW_invL (i : ℕ) (hi : BMWIndex n i) :
    ghCrossing P q aff n i false * ghCrossing P q aff n i true = 1 := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.invL (P := P) (q := q) (aff := aff) (n := n) i hi)
  simpa only [ghCrossing, presentation, map_mul, map_one] using this

theorem AuxW_invR (i : ℕ) (hi : BMWIndex n i) :
    ghCrossing P q aff n i true * ghCrossing P q aff n i false = 1 := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.invR (P := P) (q := q) (aff := aff) (n := n) i hi)
  simpa only [ghCrossing, presentation, map_mul, map_one] using this

theorem AuxW_braid (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 < n) :
    ghCrossing P q aff n i false * ghCrossing P q aff n (i+1) false * ghCrossing P q aff n i false =
    ghCrossing P q aff n (i+1) false * ghCrossing P q aff n i false * ghCrossing P q aff n (i+1) false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.braid (P := P) (q := q) (aff := aff) (n := n) i h1 h2)
  simpa only [ghCrossing, presentation, map_mul] using this

theorem AuxW_gg (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (hd : i + 1 < j ∨ j + 1 < i) :
    ghCrossing P q aff n i false * ghCrossing P q aff n j false =
    ghCrossing P q aff n j false * ghCrossing P q aff n i false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.ggFar (P := P) (q := q) (aff := aff) (n := n) i j hi hj hd)
  simpa only [ghCrossing, presentation, map_mul] using this

theorem AuxW_ge (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (hd : i + 1 < j ∨ j + 1 < i) :
    ghCrossing P q aff n i false * ghContraction P q aff n j =
    ghContraction P q aff n j * ghCrossing P q aff n i false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.geFar (P := P) (q := q) (aff := aff) (n := n) i j hi hj hd)
  simpa only [ghCrossing, ghContraction, presentation, map_mul] using this

theorem AuxW_ee (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (hd : i + 1 < j ∨ j + 1 < i) :
    ghContraction P q aff n i * ghContraction P q aff n j =
    ghContraction P q aff n j * ghContraction P q aff n i := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.eeFar (P := P) (q := q) (aff := aff) (n := n) i j hi hj hd)
  simpa only [ghContraction, presentation, map_mul] using this

theorem AuxW_tL (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (ha : BMWAdjacent i j) :
    ghCrossing P q aff n i false * ghCrossing P q aff n j false * ghContraction P q aff n i =
    ghContraction P q aff n j * ghContraction P q aff n i := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.tangleL (P := P) (q := q) (aff := aff) (n := n) i j hi hj ha)
  simpa only [ghCrossing, ghContraction, presentation, map_mul] using this

theorem AuxW_tR (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (ha : BMWAdjacent i j) :
    ghContraction P q aff n i * ghCrossing P q aff n j false * ghCrossing P q aff n i false =
    ghContraction P q aff n i * ghContraction P q aff n j := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.tangleR (P := P) (q := q) (aff := aff) (n := n) i j hi hj ha)
  simpa only [ghCrossing, ghContraction, presentation, map_mul] using this

end Rels

theorem AuxW_l39 {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R) (aff : Bool) (n : ℕ) :
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
    rw [← mul_assoc]; exact AuxW_braid P q aff n i h1 h2
  have bR : ∀ i, 1 ≤ i → i + 1 < n →
      G (i+1) * (G i * G (i+1)) = (G i * G (i+1)) * G i := by
    intro i h1 h2
    simp only [hGdef]
    rw [← mul_assoc]; exact (AuxW_braid P q aff n i h1 h2).symm
  have c2 : ∀ i, 1 ≤ i → i + 1 < n →
      E i * (G (i+1) * G i) = (G (i+1) * G i) * E (i+1) := by
    intro i h1 h2
    simp only [hGdef, hEdef]
    rw [← mul_assoc, AuxW_tR P q aff n i (i+1) ⟨h1, by omega⟩ ⟨by omega, h2⟩ (Or.inl rfl),
      AuxW_tL P q aff n (i+1) i ⟨by omega, h2⟩ ⟨h1, by omega⟩ (Or.inr rfl)]
  have c2' : ∀ i, 1 ≤ i → i + 1 < n →
      E (i+1) * (G i * G (i+1)) = (G i * G (i+1)) * E i := by
    intro i h1 h2
    simp only [hGdef, hEdef]
    rw [← mul_assoc, AuxW_tR P q aff n (i+1) i ⟨by omega, h2⟩ ⟨h1, by omega⟩ (Or.inr rfl),
      AuxW_tL P q aff n i (i+1) ⟨h1, by omega⟩ ⟨by omega, h2⟩ (Or.inl rfl)]
  have gX : ∀ i j, 1 ≤ i → i + 2 ≤ j → j < n → G i * G j = G j * G i := fun i j h1 h2 h3 =>
    AuxW_gg P q aff n i j ⟨h1, by omega⟩ ⟨by omega, h3⟩ (Or.inl (by omega))
  have gY : ∀ i j, 1 ≤ j → j + 2 ≤ i → i < n → G i * G j = G j * G i := fun i j h1 h2 h3 =>
    AuxW_gg P q aff n i j ⟨by omega, h3⟩ ⟨h1, by omega⟩ (Or.inr (by omega))
  have eX : ∀ i j, 1 ≤ i → i + 2 ≤ j → j < n → E i * G j = G j * E i := fun i j h1 h2 h3 =>
    (AuxW_ge P q aff n j i ⟨by omega, h3⟩ ⟨h1, by omega⟩ (Or.inr (by omega))).symm
  have eY : ∀ i j, 1 ≤ j → j + 2 ≤ i → i < n → E i * G j = G j * E i := fun i j h1 h2 h3 =>
    (AuxW_ge P q aff n j i ⟨h1, by omega⟩ ⟨by omega, h3⟩ (Or.inl (by omega))).symm
  have bwG := AuxW_bw G G G n gX gY bF
  have fwG := AuxW_fw G G G n gX gY bR
  have bwE := AuxW_bw G E E n eX eY c2
  have fwE := AuxW_fw G E E n eX eY c2'
  refine ⟨?_, c2, ?_, ?_, ?_⟩
  · intro i h1 h2 inv
    cases inv
    · exact bF i h1 h2
    · exact AuxW_conj (AuxW_invR P q aff n i ⟨h1, by omega⟩) (AuxW_invL P q aff n (i+1) ⟨by omega, h2⟩)
        (bF i h1 h2)
  · intro i h1 h2
    have e1 := AuxW_ee P q aff n i (i+2) ⟨h1, by omega⟩ ⟨by omega, h2⟩ (Or.inl (by omega))
    have t1 := AuxW_tL P q aff n i (i+1) ⟨h1, by omega⟩ ⟨by omega, by omega⟩ (Or.inl rfl)
    have t2 := AuxW_tL P q aff n (i+2) (i+1) ⟨by omega, h2⟩ ⟨by omega, by omega⟩ (Or.inr rfl)
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
    · exact ⟨AuxW_conj (AuxW_invR P q aff n i ⟨h1, by omega⟩) (AuxW_invL P q aff n (i+1) ⟨by omega, by omega⟩)
          (bwG m h3 i h1 h2),
        AuxW_conj (AuxW_invR P q aff n (i+1) ⟨by omega, by omega⟩) (AuxW_invL P q aff n i ⟨h1, by omega⟩)
          (fwG m h3 i h1 h2)⟩
  · intro i m h1 h2 h3
    exact ⟨bwE m h3 i h1 h2, fwE m h3 i h1 h2⟩


section Aff
variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R) (n : ℕ)

theorem AuxW_xg (j : ℕ) (hj : 2 ≤ j) (hjn : j < n) :
    bmwX P q true n false * ghCrossing P q true n j false = ghCrossing P q true n j false * bmwX P q true n false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.xgFar (P := P) (q := q) (aff := true) (n := n) rfl j hj hjn)
  simpa only [ghCrossing, bmwX, presentation, map_mul] using this

theorem AuxW_xe (j : ℕ) (hj : 2 ≤ j) (hjn : j < n) :
    bmwX P q true n false * ghContraction P q true n j = ghContraction P q true n j * bmwX P q true n false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.xeFar (P := P) (q := q) (aff := true) (n := n) rfl j hj hjn)
  simpa only [ghContraction, bmwX, presentation, map_mul] using this

theorem AuxW_ab (hn : 2 ≤ n) :
    bmwX P q true n false * ghCrossing P q true n 1 false * bmwX P q true n false * ghCrossing P q true n 1 false =
    ghCrossing P q true n 1 false * bmwX P q true n false * ghCrossing P q true n 1 false * bmwX P q true n false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.affineBraid (P := P) (q := q) (aff := true) (n := n) rfl hn)
  simpa only [ghCrossing, bmwX, presentation, map_mul] using this

theorem AuxW_def (r : ℕ) (hr : 1 ≤ r) : bmwWinding P q n false r =
    backward (fun j => ghCrossing P q true n j false) 1 (r-1) * bmwX P q true n false *
      forward (fun j => ghCrossing P q true n j false) 1 (r-1) := by
  rw [bmwWinding, if_neg (by omega)]

theorem AuxW_one : bmwWinding P q n false 1 = bmwX P q true n false := by
  rw [AuxW_def P q n 1 le_rfl]; simp [backward, forward]

theorem AuxW_succ (r : ℕ) (hr : 1 ≤ r) : bmwWinding P q n false (r+1) =
    ghCrossing P q true n r false * bmwWinding P q n false r * ghCrossing P q true n r false := by
  rw [AuxW_def P q n (r+1) (by omega), AuxW_def P q n r hr]
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have e1 : s + 1 + 1 - 1 = s + 1 := by omega
  have e2 : s + 1 - 1 = s := by omega
  rw [e1, e2, AuxW_bws, AuxW_fws]
  have e3 : 1 + s = s + 1 := by omega
  rw [e3]; simp only [mul_assoc]

theorem AuxW_C1 (r j : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ n) (hj : BMWIndex n j) (hne1 : j ≠ r) (hne2 : j + 1 ≠ r) :
    ghCrossing P q true n j false * bmwWinding P q n false r =
      bmwWinding P q n false r * ghCrossing P q true n j false := by
  rw [AuxW_def P q n r h1]
  have L := AuxW_l39 P q true n
  have hj1 := hj.1
  have hj2 := hj.2
  rcases (show r + 1 ≤ j ∨ j + 2 ≤ r by omega) with hf | hc
  · have cB := AuxW_bwc (fun j => ghCrossing P q true n j false) (ghCrossing P q true n j false) (r-1)
      (fun i hi1 hi2 => AuxW_gg P q true n j i hj ⟨hi1, by omega⟩ (Or.inr (by omega)))
    have cF := AuxW_fwc (fun j => ghCrossing P q true n j false) (ghCrossing P q true n j false) (r-1)
      (fun i hi1 hi2 => AuxW_gg P q true n j i hj ⟨hi1, by omega⟩ (Or.inr (by omega)))
    have cX := (AuxW_xg P q n j (by omega) hj.2).symm
    exact (Commute.mul_right (Commute.mul_right cB cX) cF).eq
  · have hb := (L.2.2.2.1 j (r-1) hj.1 (by omega) (by omega) false).1
    have hf := (L.2.2.2.1 j (r-1) hj.1 (by omega) (by omega) false).2
    have cX := (AuxW_xg P q n (j+1) (by omega) (by omega)).symm
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

theorem AuxW_C2 (r j : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ n) (hj : BMWIndex n j) (hne1 : j ≠ r) (hne2 : j + 1 ≠ r) :
    ghContraction P q true n j * bmwWinding P q n false r =
      bmwWinding P q n false r * ghContraction P q true n j := by
  rw [AuxW_def P q n r h1]
  have L := AuxW_l39 P q true n
  have hj1 := hj.1
  have hj2 := hj.2
  rcases (show r + 1 ≤ j ∨ j + 2 ≤ r by omega) with hf | hc
  · have cB := AuxW_bwc (fun j => ghCrossing P q true n j false) (ghContraction P q true n j) (r-1)
      (fun i hi1 hi2 => (AuxW_ge P q true n i j ⟨hi1, by omega⟩ hj (Or.inl (by omega))).symm)
    have cF := AuxW_fwc (fun j => ghCrossing P q true n j false) (ghContraction P q true n j) (r-1)
      (fun i hi1 hi2 => (AuxW_ge P q true n i j ⟨hi1, by omega⟩ hj (Or.inl (by omega))).symm)
    have cX := (AuxW_xe P q n j (by omega) hj.2).symm
    exact (Commute.mul_right (Commute.mul_right cB cX) cF).eq
  · have hb := (L.2.2.2.2 j (r-1) hj.1 (by omega) (by omega)).1
    have hf := (L.2.2.2.2 j (r-1) hj.1 (by omega) (by omega)).2
    have cX := (AuxW_xe P q n (j+1) (by omega) (by omega)).symm
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

theorem AuxW_mon {A : Type*} [Monoid A] {a b x : A} (hb : a*b*a = b*a*b) (hxb : x*b = b*x)
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

theorem AuxW_adj (r : ℕ) (hr : 1 ≤ r) : r + 1 ≤ n →
    bmwWinding P q n false r * bmwWinding P q n false (r+1) =
      bmwWinding P q n false (r+1) * bmwWinding P q n false r := by
  induction r, hr using Nat.le_induction with
  | base =>
    intro hn
    rw [AuxW_succ P q n 1 le_rfl, AuxW_one]
    have := AuxW_ab P q n hn
    simp only [mul_assoc] at this ⊢
    exact this
  | succ s hs ih =>
    intro hn
    have ih' := ih (by omega)
    rw [AuxW_succ P q n (s+1) (by omega), AuxW_succ P q n s hs]
    rw [AuxW_succ P q n s hs] at ih'
    apply AuxW_mon
    · exact AuxW_braid P q true n s hs (by omega)
    · exact (AuxW_C1 P q n s (s+1) hs (by omega) ⟨by omega, by omega⟩ (by omega) (by omega)).symm
    · simp only [mul_assoc] at ih' ⊢; exact ih'

theorem AuxW_far (d : ℕ) : ∀ j, 1 ≤ j → j + d + 1 ≤ n →
    Commute (bmwWinding P q n false j) (bmwWinding P q n false (j+d+1)) := by
  induction d with
  | zero => intro j hj hn; exact AuxW_adj P q n j hj (by omega)
  | succ d ih =>
    intro j hj hn
    have e : j + (d+1) + 1 = (j+d+1) + 1 := by omega
    rw [e, AuxW_succ P q n (j+d+1) (by omega)]
    have cg : Commute (bmwWinding P q n false j) (ghCrossing P q true n (j+d+1) false) :=
      (AuxW_C1 P q n j (j+d+1) hj (by omega) ⟨by omega, by omega⟩ (by omega) (by omega)).symm
    exact (cg.mul_right (ih j hj (by omega))).mul_right cg

theorem _root_.solution {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R) (n : ℕ) :
    (∀ r j, 1 ≤ r → r ≤ n → BMWIndex n j → j ≠ r → j+1 ≠ r →
      ghCrossing P q true n j false * bmwWinding P q n false r =
        bmwWinding P q n false r * ghCrossing P q true n j false) ∧
    (∀ r j, 1 ≤ r → r ≤ n → BMWIndex n j → j ≠ r → j+1 ≠ r →
      ghContraction P q true n j * bmwWinding P q n false r =
        bmwWinding P q n false r * ghContraction P q true n j) ∧
    (∀ r j, 1 ≤ r → r ≤ n → 1 ≤ j → j ≤ n →
      bmwWinding P q n false j * bmwWinding P q n false r =
        bmwWinding P q n false r * bmwWinding P q n false j) := by
  refine ⟨fun r j h1 h2 hj a b => AuxW_C1 P q n r j h1 h2 hj a b,
    fun r j h1 h2 hj a b => AuxW_C2 P q n r j h1 h2 hj a b, ?_⟩
  intro r j h1 h2 h3 h4
  rcases lt_trichotomy j r with h | h | h
  · obtain ⟨d, rfl⟩ : ∃ d, r = j + d + 1 := ⟨r - j - 1, by omega⟩
    exact (AuxW_far P q n d j h3 h2).eq
  · subst h; rfl
  · obtain ⟨d, rfl⟩ : ∃ d, j = r + d + 1 := ⟨j - r - 1, by omega⟩
    exact (AuxW_far P q n d r h1 h4).eq.symm

end Aff2

end QAlgorithms.Papers.Independent.Intake100.P55
