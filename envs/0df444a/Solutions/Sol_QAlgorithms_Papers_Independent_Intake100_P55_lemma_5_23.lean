-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P55.lemma_5_23
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T11:38:46.492304+00:00
-- url     : https://prove2.me/submissions/f833fc58-51d6-4287-a8c3-df5b4dfa46ec

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55
noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Mon
variable {A : Type*} [Monoid A]

theorem AuxK_bws (h : ℕ → A) (a m : ℕ) : backward h a (m+1) = h (a+m) * backward h a m := by
  simp [backward, List.range_succ]

theorem AuxK_fws (h : ℕ → A) (a m : ℕ) : forward h a (m+1) = forward h a m * h (a+m) := by
  simp [forward, List.range_succ]

end Mon

section Rels
variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R) (aff : Bool) (n : ℕ)

theorem AuxK_invL (i : ℕ) (hi : BMWIndex n i) :
    ghCrossing P q aff n i false * ghCrossing P q aff n i true = 1 := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.invL (P := P) (q := q) (aff := aff) (n := n) i hi)
  simpa only [ghCrossing, presentation, map_mul, map_one] using this

theorem AuxK_invR (i : ℕ) (hi : BMWIndex n i) :
    ghCrossing P q aff n i true * ghCrossing P q aff n i false = 1 := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.invR (P := P) (q := q) (aff := aff) (n := n) i hi)
  simpa only [ghCrossing, presentation, map_mul, map_one] using this

theorem AuxK_braid (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 < n) :
    ghCrossing P q aff n i false * ghCrossing P q aff n (i+1) false * ghCrossing P q aff n i false =
    ghCrossing P q aff n (i+1) false * ghCrossing P q aff n i false * ghCrossing P q aff n (i+1) false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.braid (P := P) (q := q) (aff := aff) (n := n) i h1 h2)
  simpa only [ghCrossing, presentation, map_mul] using this

theorem AuxK_gg (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (hd : i + 1 < j ∨ j + 1 < i) :
    ghCrossing P q aff n i false * ghCrossing P q aff n j false =
    ghCrossing P q aff n j false * ghCrossing P q aff n i false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.ggFar (P := P) (q := q) (aff := aff) (n := n) i j hi hj hd)
  simpa only [ghCrossing, presentation, map_mul] using this

theorem AuxK_ge (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (hd : i + 1 < j ∨ j + 1 < i) :
    ghCrossing P q aff n i false * ghContraction P q aff n j =
    ghContraction P q aff n j * ghCrossing P q aff n i false := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.geFar (P := P) (q := q) (aff := aff) (n := n) i j hi hj hd)
  simpa only [ghCrossing, ghContraction, presentation, map_mul] using this

theorem AuxK_ee (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (hd : i + 1 < j ∨ j + 1 < i) :
    ghContraction P q aff n i * ghContraction P q aff n j =
    ghContraction P q aff n j * ghContraction P q aff n i := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.eeFar (P := P) (q := q) (aff := aff) (n := n) i j hi hj hd)
  simpa only [ghContraction, presentation, map_mul] using this

theorem AuxK_tL (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (ha : BMWAdjacent i j) :
    ghCrossing P q aff n i false * ghCrossing P q aff n j false * ghContraction P q aff n i =
    ghContraction P q aff n j * ghContraction P q aff n i := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.tangleL (P := P) (q := q) (aff := aff) (n := n) i j hi hj ha)
  simpa only [ghCrossing, ghContraction, presentation, map_mul] using this

theorem AuxK_tR (i j : ℕ) (hi : BMWIndex n i) (hj : BMWIndex n j) (ha : BMWAdjacent i j) :
    ghContraction P q aff n i * ghCrossing P q aff n j false * ghCrossing P q aff n i false =
    ghContraction P q aff n i * ghContraction P q aff n j := by
  have := RingQuot.mkAlgHom_rel R (OrdinaryAffineBMWRel.tangleR (P := P) (q := q) (aff := aff) (n := n) i j hi hj ha)
  simpa only [ghCrossing, ghContraction, presentation, map_mul] using this

end Rels

theorem AuxK_main {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R) (n : ℕ) :
    ∀ k, 2*k < n →
    forward (fun i => ghCrossing P q false n i false) 1 (2*k) * oddContractions P q n k =
      ((List.range k).map fun j => ghContraction P q false n (2*j+2)).prod * oddContractions P q n k ∧
    oddContractions P q n k * backward (fun i => ghCrossing P q false n i false) 1 (2*k) =
      oddContractions P q n k * ((List.range k).map fun j => ghContraction P q false n (2*j+2)).prod := by
  intro k
  induction k with
  | zero => intro _; simp [forward, backward, oddContractions]
  | succ k ih =>
    intro hn
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    set G : ℕ → OrdinaryAffineBMW P q false n := fun i => ghCrossing P q false n i false with hG
    set E : ℕ → OrdinaryAffineBMW P q false n := fun i => ghContraction P q false n i with hE
    have hOD : oddContractions P q n (k+1) = oddContractions P q n k * E (2*k+1) := by
      simp [oddContractions, List.range_succ, hE]
    have hEV : ((List.range (k+1)).map fun j => ghContraction P q false n (2*j+2)).prod =
        ((List.range k).map fun j => ghContraction P q false n (2*j+2)).prod * E (2*k+2) := by
      simp [List.range_succ, hE]
    have e2 : 2*(k+1) = 2*k+1+1 := by ring
    have hF : forward G 1 (2*(k+1)) = forward G 1 (2*k) * G (2*k+1) * G (2*k+2) := by
      rw [e2, AuxK_fws, AuxK_fws]
      have a1 : 1 + (2*k+1) = 2*k+2 := by omega
      have a2 : 1 + 2*k = 2*k+1 := by omega
      rw [a1, a2]
    have hB : backward G 1 (2*(k+1)) = G (2*k+2) * (G (2*k+1) * backward G 1 (2*k)) := by
      rw [e2, AuxK_bws, AuxK_bws]
      have a1 : 1 + (2*k+1) = 2*k+2 := by omega
      have a2 : 1 + 2*k = 2*k+1 := by omega
      rw [a1, a2]
    have cGO : ∀ a, 2*k+1 ≤ a → a < n → Commute (G a) (oddContractions P q n k) := by
      intro a ha1 ha2
      unfold oddContractions
      apply Commute.list_prod_right
      intro y hy
      simp only [List.mem_map, List.mem_range] at hy
      obtain ⟨j, hj, rfl⟩ := hy
      exact AuxK_ge P q false n a (2*j+1) ⟨by omega, ha2⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
    have cEO : ∀ a, 2*k+1 ≤ a → a < n → Commute (E a) (oddContractions P q n k) := by
      intro a ha1 ha2
      unfold oddContractions
      apply Commute.list_prod_right
      intro y hy
      simp only [List.mem_map, List.mem_range] at hy
      obtain ⟨j, hj, rfl⟩ := hy
      exact AuxK_ee P q false n a (2*j+1) ⟨by omega, ha2⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
    have cEV : Commute (E (2*k+2)) ((List.range k).map fun j => ghContraction P q false n (2*j+2)).prod := by
      apply Commute.list_prod_right
      intro y hy
      simp only [List.mem_map, List.mem_range] at hy
      obtain ⟨j, hj, rfl⟩ := hy
      exact AuxK_ee P q false n (2*k+2) (2*j+2) ⟨by omega, hn⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
    have cG12 : Commute (G (2*k+1) * G (2*k+2)) (oddContractions P q n k) :=
      (cGO _ le_rfl (by omega)).mul_left (cGO _ (by omega) hn)
    have cG21 : Commute (G (2*k+2) * G (2*k+1)) (oddContractions P q n k) :=
      (cGO _ (by omega) hn).mul_left (cGO _ le_rfl (by omega))
    have cE1 := cEO (2*k+1) le_rfl (by omega)
    have cE2 := cEO (2*k+2) (by omega) hn
    have tL : G (2*k+1) * G (2*k+2) * E (2*k+1) = E (2*k+2) * E (2*k+1) :=
      AuxK_tL P q false n (2*k+1) (2*k+2) ⟨by omega, by omega⟩ ⟨by omega, hn⟩ (Or.inl rfl)
    have tR : E (2*k+1) * G (2*k+2) * G (2*k+1) = E (2*k+1) * E (2*k+2) :=
      AuxK_tR P q false n (2*k+1) (2*k+2) ⟨by omega, by omega⟩ ⟨by omega, hn⟩ (Or.inl rfl)
    set OD := oddContractions P q n k with hODd
    set EV := ((List.range k).map fun j => ghContraction P q false n (2*j+2)).prod with hEVd
    constructor
    · calc forward G 1 (2*(k+1)) * oddContractions P q n (k+1)
          = forward G 1 (2*k) * ((G (2*k+1) * G (2*k+2)) * OD) * E (2*k+1) := by
            rw [hF, hOD]; simp only [mul_assoc]
        _ = forward G 1 (2*k) * (OD * (G (2*k+1) * G (2*k+2))) * E (2*k+1) := by rw [cG12.eq]
        _ = (forward G 1 (2*k) * OD) * (G (2*k+1) * G (2*k+2) * E (2*k+1)) := by simp only [mul_assoc]
        _ = (EV * OD) * (E (2*k+2) * E (2*k+1)) := by rw [ih1, tL]
        _ = EV * (E (2*k+2) * OD) * E (2*k+1) := by rw [cE2.eq]; simp only [mul_assoc]
        _ = _ := by rw [hEV, hOD]; simp only [mul_assoc]
    · calc oddContractions P q n (k+1) * backward G 1 (2*(k+1))
          = (E (2*k+1) * OD) * ((G (2*k+2) * G (2*k+1)) * backward G 1 (2*k)) := by
            rw [hOD, hB, cE1.eq]; simp only [mul_assoc]
        _ = E (2*k+1) * ((OD * (G (2*k+2) * G (2*k+1))) * backward G 1 (2*k)) := by simp only [mul_assoc]
        _ = E (2*k+1) * (((G (2*k+2) * G (2*k+1)) * OD) * backward G 1 (2*k)) := by rw [← cG21.eq]
        _ = (E (2*k+1) * G (2*k+2) * G (2*k+1)) * (OD * backward G 1 (2*k)) := by simp only [mul_assoc]
        _ = (E (2*k+1) * E (2*k+2)) * (OD * EV) := by rw [tR, ih2]
        _ = E (2*k+1) * (E (2*k+2) * OD) * EV := by simp only [mul_assoc]
        _ = E (2*k+1) * (OD * E (2*k+2)) * EV := by rw [cE2.eq]
        _ = (E (2*k+1) * OD) * (E (2*k+2) * EV) := by simp only [mul_assoc]
        _ = (OD * E (2*k+1)) * (EV * E (2*k+2)) := by rw [cE1.eq, cEV.eq]
        _ = _ := by rw [hEV, hOD]

theorem _root_.solution {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R) (n k : ℕ) (hn : 2*k < n) :
    let g := fun i => ghCrossing P q false n i false
    let e := ghContraction P q false n
    let odd := oddContractions P q n k
    let even := ((List.range k).map fun j => e (2*j+2)).prod
    forward g 1 (2*k) * odd = even * odd ∧
    odd * backward g 1 (2*k) = odd * even := by
  intro g e odd even
  exact AuxK_main P q n k hn

end QAlgorithms.Papers.Independent.Intake100.P55
