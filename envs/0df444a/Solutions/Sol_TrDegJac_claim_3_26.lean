-- Prove2me | solution 1 for TrDegJac.claim_3_26
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T04:10:51.582014+00:00
-- url     : https://prove2.me/submissions/bc4cc0b3-3b06-4d92-8a51-733e210a5a26

import Mathlib

set_option autoImplicit false

open scoped BigOperators

theorem solution (n N : ℕ) (w : Fin n → ℕ) (hw : ∀ i, 1 ≤ w i) :
    ((n + N).choose n : ℚ) / ∏ i, (w i : ℚ) ≤
      ({a : Fin n → ℕ | ∑ i, w i * a i ≤ N}.ncard : ℚ) := by
  classical
  -- The unweighted exponent vectors with sum ≤ N, assembled from exact-sum slices.
  set Af : Finset (Fin n → ℕ) :=
    (Finset.range (N + 1)).biUnion
      (fun k => Finset.piAntidiag (Finset.univ : Finset (Fin n)) k) with hAf
  -- The box of exponent vectors with all coordinates ≤ N.
  set box : Finset (Fin n → ℕ) :=
    Fintype.piFinset (fun _ : Fin n => Finset.range (N + 1)) with hbox
  -- The weighted exponent vectors with weighted sum ≤ N.
  set Bf : Finset (Fin n → ℕ) :=
    box.filter (fun a => ∑ i, w i * a i ≤ N) with hBf
  -- The quotient map and the remainder map.
  set phi : (Fin n → ℕ) → (Fin n → ℕ) := fun a i => a i / w i with hphi
  set rho : (Fin n → ℕ) → (Fin n → ℕ) := fun a i => a i % w i with hrho
  have mem_box : ∀ a : Fin n → ℕ, a ∈ box ↔ ∀ i, a i ≤ N := by
    intro a
    simp [hbox, Fintype.mem_piFinset]
  have mem_Af : ∀ a : Fin n → ℕ, a ∈ Af ↔ ∑ i, a i ≤ N := by
    intro a
    rw [hAf]
    constructor
    · intro ha
      obtain ⟨k, hk, hmem⟩ := Finset.mem_biUnion.1 ha
      rw [Finset.mem_range] at hk
      rw [Finset.mem_piAntidiag] at hmem
      have hsum : ∑ i, a i = k := by simpa using hmem.1
      omega
    · intro h
      refine Finset.mem_biUnion.2 ⟨∑ i, a i, ?_, ?_⟩
      · rw [Finset.mem_range]; omega
      · rw [Finset.mem_piAntidiag]
        exact ⟨by simp, fun i _ => Finset.mem_univ i⟩
  have mem_Bf : ∀ a : Fin n → ℕ, a ∈ Bf ↔ ∑ i, w i * a i ≤ N := by
    intro a
    rw [hBf, Finset.mem_filter, mem_box]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h
      refine ⟨fun i => ?_, h⟩
      have h1 : w i * a i ≤ ∑ j, w j * a j :=
        Finset.single_le_sum (f := fun j => w j * a j) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
      have h2 : a i ≤ w i * a i :=
        Nat.le_mul_of_pos_left (a i) (by have := hw i; omega)
      omega
  have hAeq : {a : Fin n → ℕ | ∑ i, a i ≤ N} = ↑Af := by
    ext a
    simp [mem_Af]
  have hBeq : {a : Fin n → ℕ | ∑ i, w i * a i ≤ N} = ↑Bf := by
    ext a
    simp [mem_Bf]
  -- Cardinality of one exact-sum slice: it is a multichoose count.
  have hper : ∀ k : ℕ,
      (Finset.piAntidiag (Finset.univ : Finset (Fin n)) k).card = n.multichoose k := by
    intro k
    rw [← Finset.map_sym_eq_piAntidiag (Finset.univ : Finset (Fin n)) k, Finset.card_map,
      Finset.sym_univ, Finset.card_univ, Sym.card_sym_eq_multichoose]
    simp
  have hAfcard : Af.card = (N + n).choose n := by
    rw [hAf, Finset.card_biUnion
      (t := fun k => Finset.piAntidiag (Finset.univ : Finset (Fin n)) k)]
    · calc ∑ k ∈ Finset.range (N + 1),
            (Finset.piAntidiag (Finset.univ : Finset (Fin n)) k).card
          = ∑ k ∈ Finset.range (N + 1), n.multichoose k :=
            Finset.sum_congr rfl (fun k _ => hper k)
        _ = (N + n).choose n := Nat.sum_range_multichoose N n
    · intro k _ k' _ hkk'
      refine Finset.disjoint_left.2 (fun a ha ha' => ?_)
      rw [Finset.mem_piAntidiag] at ha ha'
      exact hkk' (by rw [← ha.1, ← ha'.1])
  -- Every fibre of `phi` inside `Af` injects into `∏ i, Fin (w i)`.
  have hfib : ∀ b ∈ Bf, (Af.filter (fun a => phi a = b)).card ≤ ∏ i, w i := by
    intro b _
    have hmaps : ∀ a ∈ Af.filter (fun a => phi a = b),
        rho a ∈ Fintype.piFinset (fun i : Fin n => Finset.range (w i)) := by
      intro a _
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_range]
      simp only [hrho]
      exact Nat.mod_lt _ (by have := hw i; omega)
    have hinj : ∀ a ∈ Af.filter (fun a => phi a = b),
        ∀ a' ∈ Af.filter (fun a => phi a = b), rho a = rho a' → a = a' := by
      intro a ha a' ha' heq
      have hpa : phi a = b := (Finset.mem_filter.1 ha).2
      have hpa' : phi a' = b := (Finset.mem_filter.1 ha').2
      have hdiv : ∀ i, a i / w i = a' i / w i := by
        intro i
        have h : phi a = phi a' := by rw [hpa, hpa']
        have := congr_fun h i
        simpa [hphi] using this
      have hmod : ∀ i, a i % w i = a' i % w i := by
        intro i
        have := congr_fun heq i
        simpa [hrho] using this
      funext i
      calc a i = w i * (a i / w i) + a i % w i := (Nat.div_add_mod (a i) (w i)).symm
        _ = w i * (a' i / w i) + a' i % w i := by rw [hdiv i, hmod i]
        _ = a' i := Nat.div_add_mod (a' i) (w i)
    calc (Af.filter (fun a => phi a = b)).card
        ≤ (Fintype.piFinset (fun i : Fin n => Finset.range (w i))).card :=
          Finset.card_le_card_of_injOn rho
            (by intro a ha; exact hmaps a (by simpa using ha))
            (by intro a ha a' ha' heq; exact hinj a (by simpa using ha) a' (by simpa using ha') heq)
      _ = ∏ i, w i := by rw [Fintype.card_piFinset]; simp
  -- `phi` maps `Af` into `Bf`.
  have hphi_mem : ∀ a ∈ Af, phi a ∈ Bf := by
    intro a ha
    rw [mem_Bf]
    have h1 : ∑ i, w i * phi a i ≤ ∑ i, a i := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      simp only [hphi]
      exact Nat.mul_div_le (a i) (w i)
    exact le_trans h1 ((mem_Af a).1 ha)
  have hkey : Af.card ≤ (∏ i, w i) * Bf.card :=
    Finset.card_le_mul_card_image_of_maps_to (f := phi) (s := Af) (t := Bf)
      hphi_mem (∏ i, w i) hfib
  have hAnat : {a : Fin n → ℕ | ∑ i, a i ≤ N}.ncard = Af.card := by
    rw [hAeq, Set.ncard_coe_finset]
  have hBnat : {a : Fin n → ℕ | ∑ i, w i * a i ≤ N}.ncard = Bf.card := by
    rw [hBeq, Set.ncard_coe_finset]
  have hprodpos : (0 : ℚ) < ∏ i, (w i : ℚ) := by
    refine Finset.prod_pos (fun i _ => ?_)
    have := hw i
    exact_mod_cast (show 0 < w i by omega)
  rw [div_le_iff₀ hprodpos, hBnat]
  have hfin : ((n + N).choose n : ℚ) ≤ (Bf.card : ℚ) * ∏ i, (w i : ℚ) := by
    have h := hkey
    rw [hAfcard] at h
    have hcast : ((N + n).choose n : ℚ) ≤ ((∏ i, w i) * Bf.card : ℕ) := by
      exact_mod_cast h
    calc ((n + N).choose n : ℚ) = ((N + n).choose n : ℚ) := by rw [Nat.add_comm]
      _ ≤ ((∏ i, w i) * Bf.card : ℕ) := hcast
      _ = (Bf.card : ℚ) * ∏ i, (w i : ℚ) := by push_cast; ring
  exact hfin
