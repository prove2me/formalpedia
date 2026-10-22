-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P08.directed_projectors
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:14:38.624979+00:00
-- url     : https://prove2.me/submissions/5930e896-5b0f-4333-9219-702cd6e9ac23

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08
noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section G67E
open Polynomial

variable {R : Type*} [CommRing R] {d : ℕ}

lemma g67e_diag_mul (A B : Matrix (Fin d) (Fin d) R) (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (a : Fin d) : (A * B) a a = A a a * B a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

lemma g67e_list_prod (l : List (Matrix (Fin d) (Fin d) R))
    (h : ∀ M ∈ l, M.BlockTriangular id) :
    l.prod.BlockTriangular id ∧ ∀ a, l.prod a a = (l.map (fun M => M a a)).prod := by
  induction l with
  | nil => exact ⟨Matrix.blockTriangular_one, fun a => by simp⟩
  | cons M l ih =>
    have hM := h M (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := ih (fun N hN => h N (List.mem_cons_of_mem _ hN))
    refine ⟨by rw [List.prod_cons]; exact hM.mul h1, fun a => ?_⟩
    rw [List.prod_cons, g67e_diag_mul _ _ hM h1, h2, List.map_cons, List.prod_cons]

lemma g67e_diag_pow (A : Matrix (Fin d) (Fin d) R) (hA : A.BlockTriangular id) (a : Fin d) :
    ∀ m : ℕ, (A ^ m) a a = (A a a) ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, g67e_diag_mul _ _ (hA.pow m) hA, ih, pow_succ]

lemma g67e_charpoly_ann (Z : Matrix (Fin d) (Fin d) R) (hZ : Z.BlockTriangular id)
    (J : Finset (Fin d)) (hdiag : ∀ i, Z i i = if i ∈ J then 1 else 0) :
    Polynomial.aeval Z ((Polynomial.X - 1) ^ J.card * Polynomial.X ^ (d - J.card) : Polynomial R) = 0 := by
  have hc : Z.charpoly = (Polynomial.X - 1) ^ J.card * Polynomial.X ^ (d - J.card) := by
    rw [Matrix.charpoly_of_isUpperTriangular Z hZ]
    simp_rw [hdiag]
    have : ∀ i : Fin d, (X - C (if i ∈ J then (1:R) else 0)) = if i ∈ J then (X - 1) else X := by
      intro i; split_ifs <;> simp
    simp_rw [this]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    congr 2
    · congr 1; ext x; simp
    · rw [show (Finset.univ.filter fun x : Fin d => x ∉ J) = Jᶜ by ext x; simp,
        Finset.card_compl, Fintype.card_fin]
  rw [← hc]; exact Matrix.aeval_self_charpoly Z

lemma g67e_pow_zero_left (Z : Matrix (Fin d) (Fin d) R) (hZ : Z.BlockTriangular id) (b : Fin d)
    (h0 : ∀ k : Fin d, k ≤ b → Z k k = 0) :
    ∀ m : ℕ, ∀ a : Fin d, b.val < a.val + m → (Z ^ m) a b = 0 := by
  intro m
  induction m with
  | zero =>
    intro a hab
    simp only [pow_zero]
    exact Matrix.one_apply_ne (by intro h; subst h; omega)
  | succ m ih =>
    intro a hab
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_trichotomy k a with h | h | h
    · rw [hZ h, zero_mul]
    · subst h
      by_cases hk : k ≤ b
      · rw [h0 k hk, zero_mul]
      · rw [ih k (by push Not at hk; exact Nat.lt_of_lt_of_le hk (Nat.le_add_right _ _)), mul_zero]
    · rw [ih k (by have : a.val < k.val := h; omega), mul_zero]

lemma g67e_pow_zero_right (Z : Matrix (Fin d) (Fin d) R) (hZ : Z.BlockTriangular id) (a : Fin d)
    (h0 : ∀ k : Fin d, a ≤ k → Z k k = 0) :
    ∀ m : ℕ, ∀ b : Fin d, b.val < a.val + m → (Z ^ m) a b = 0 := by
  intro m
  induction m with
  | zero =>
    intro b hab
    simp only [pow_zero]
    exact Matrix.one_apply_ne (by intro h; subst h; omega)
  | succ m ih =>
    intro b hab
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_trichotomy k b with h | h | h
    · rw [ih k (by have : k.val < b.val := h; omega), zero_mul]
    · subst h
      by_cases hk : a ≤ k
      · rw [h0 k hk, mul_zero]
      · rw [ih k (by push Not at hk; exact Nat.lt_of_lt_of_le hk (Nat.le_add_right _ _)), zero_mul]
    · rw [hZ h, mul_zero]

lemma g67e_stable (Z : Matrix (Fin d) (Fin d) R) (hd : 1 ≤ d) (h : Z ^ d = Z ^ (d - 1)) :
    ∀ j : ℕ, Z ^ (d + j) = Z ^ d := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have e : Z * Z ^ (d - 1) = Z ^ d := by rw [← pow_succ']; congr 1; omega
    rw [← add_assoc, pow_succ, ih, ← pow_succ, pow_succ', h, e, h]

lemma g67e_idem_of_card_one (Z : Matrix (Fin d) (Fin d) R) (hZ : Z.BlockTriangular id)
    (J : Finset (Fin d)) (hdiag : ∀ i, Z i i = if i ∈ J then 1 else 0) (hJ : J.card = 1) :
    Z ^ d = Z ^ (d - 1) ∧ (∀ j : ℕ, 1 ≤ j → Z ^ (d + j) = Z ^ d) ∧
      (Z ^ d) * (Z ^ d) = Z ^ d := by
  have hd : 1 ≤ d := by
    have := Finset.card_le_univ J; rw [Fintype.card_fin] at this; omega
  have h := g67e_charpoly_ann Z hZ J hdiag
  rw [hJ, pow_one] at h
  simp only [map_mul, map_sub, Polynomial.aeval_X, map_one, map_pow] at h
  have h1 : Z ^ d = Z ^ (d - 1) := by
    have : Z ^ d = Z * Z ^ (d - 1) := by rw [← pow_succ']; congr 1; omega
    rw [this]; rw [sub_mul, one_mul, sub_eq_zero] at h; exact h
  refine ⟨h1, fun j _ => g67e_stable Z hd h1 j, ?_⟩
  rw [← pow_add]; exact g67e_stable Z hd h1 d

lemma g67e_shape_of_diag (Z : Matrix (Fin d) (Fin d) R) (hZ : Z.BlockTriangular id) (i : Fin d)
    (hdiag : ∀ a, Z a a = if a = i then 1 else 0) :
    HasShape (Z ^ d) {i} ∧ Z ^ d * Z ^ d = Z ^ d := by
  have hdiag' : ∀ a, Z a a = if a ∈ ({i} : Finset (Fin d)) then 1 else 0 := by
    intro a; rw [hdiag a]; simp
  refine ⟨⟨Finset.singleton_nonempty i, ?_, ?_⟩,
    (g67e_idem_of_card_one Z hZ {i} hdiag' (Finset.card_singleton i)).2.2⟩
  · intro a b hab
    refine ⟨i, Finset.mem_singleton_self i, ?_, ?_⟩
    · by_contra hc; push Not at hc
      exact hab (g67e_pow_zero_right Z hZ a (fun k hk => by
        rw [hdiag k, if_neg]; intro h; subst h; exact absurd hk (not_le.mpr hc)) d b
        (by have := b.isLt; omega))
    · by_contra hc; push Not at hc
      exact hab (g67e_pow_zero_left Z hZ b (fun k hk => by
        rw [hdiag k, if_neg]; intro h; subst h; exact absurd hk (not_le.mpr hc)) d a
        (by have := b.isLt; omega))
  · intro a
    rw [g67e_diag_pow Z hZ a d, hdiag a]
    have : d ≠ 0 := by have := a.isLt; omega
    by_cases h : a = i <;> simp [h, this]

lemma g67e_interp_upper {n : ℕ} (S : TriangularSystem R d n) (C : SeparatingChoices S) (i : Fin d) :
    (interpolation S C i).BlockTriangular id ∧
    ∀ a, interpolation S C i a a = if a = i then 1 else 0 := by
  have hup : ∀ M ∈ (C.order i).map (fun j => if h : i ≠ j then
      ((C.denominator i j h)⁻¹ : Rˣ).val •
        (S.L (C.position i j h) -
          algebraMap R (Matrix (Fin d) (Fin d) R) (triangularDiagonalEntry S (C.position i j h) j))
      else 1), M.BlockTriangular id := by
    intro M hM
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hM
    by_cases h : i ≠ j
    · rw [dif_pos h]
      intro a b hab
      have hab' : b < a := hab
      simp [S.upper _ _ _ hab', Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply_ne _ (ne_of_lt hab').symm]
    · rw [dif_neg h]; exact Matrix.blockTriangular_one
  obtain ⟨h1, h2⟩ := g67e_list_prod _ hup
  refine ⟨h1, fun a => ?_⟩
  unfold interpolation
  rw [h2, List.map_map]
  by_cases ha : a = i
  · subst ha
    rw [if_pos rfl]
    apply List.prod_eq_one
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hij : a ≠ j := ((C.members a j).mp hj).symm
    simp only [Function.comp, dif_pos hij]
    rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.algebraMap_eq_diagonal]
    simp only [Pi.algebraMap_apply, Matrix.diagonal_apply_eq, Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul]
    rw [show S.L (C.position a j hij) a a - triangularDiagonalEntry S (C.position a j hij) j
      = (C.denominator a j hij : R) by rw [C.denominator_value]; rfl]
    simp
  · rw [if_neg ha]
    apply List.prod_eq_zero
    have hm : a ∈ C.order i := (C.members i a).mpr ha
    refine List.mem_map.mpr ⟨a, hm, ?_⟩
    have hia : i ≠ a := fun h => ha h.symm
    simp only [Function.comp, dif_pos hia]
    rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.algebraMap_eq_diagonal]
    simp [triangularDiagonalEntry]

end G67E

section AppendixDefinitions

variable {R : Type*} [CommRing R]

theorem solution [IsDomain R] {d n : ℕ}
    (S : TriangularSystem R d n) (C : SeparatingChoices S) :
    DirectedFamily (directedProjector S C) := by
  have key : ∀ i, directedProjector S C i * directedProjector S C i = directedProjector S C i ∧
      HasShape (directedProjector S C i) {i} := by
    intro i
    obtain ⟨h1, h2⟩ := g67e_interp_upper S C i
    obtain ⟨h3, h4⟩ := g67e_shape_of_diag _ h1 i h2
    exact ⟨h4, h3⟩
  refine ⟨fun i => (key i).1, fun i j hij => ?_⟩
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases h1 : directedProjector S C j a k = 0
  · rw [h1, zero_mul]
  by_cases h2 : directedProjector S C i k b = 0
  · rw [h2, mul_zero]
  exfalso
  obtain ⟨x, hx, _, hxk⟩ := (key j).2.2.1 a k h1
  obtain ⟨y, hy, hky, _⟩ := (key i).2.2.1 k b h2
  rw [Finset.mem_singleton] at hx hy
  subst hx hy
  exact absurd (le_trans hxk hky) (not_le.mpr hij)

end AppendixDefinitions

end
