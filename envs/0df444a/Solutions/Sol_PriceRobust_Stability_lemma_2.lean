-- Prove2me | solution 1 for PriceRobust.Stability.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:05:14.84617+00:00
-- url     : https://prove2.me/submissions/bbef06b2-803b-4ad3-9d2e-ba0521b6e25d

import Mathlib
import Definitions.Def_PriceRobust_Stability_ZPMatrix
import Definitions.Def_PriceRobust_Stability_Model

open Matrix

namespace PRB1
open PriceRobust.Stability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Schur complement of `A` at the pivot `k`. -/
noncomputable def schur (A : Matrix ι ι ℝ) (k : ι) : Matrix {i // i ≠ k} {i // i ≠ k} ℝ :=
  fun i j => A i j - A i k * A k j / A k k

lemma sum_split (f : ι → ℝ) (k : ι) : ∑ j, f j = f k + ∑ j : {j // j ≠ k}, f j.1 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), add_comm]
  congr 1
  exact Finset.sum_subtype _ (fun j => by simp [Finset.mem_erase]) f

/-- The principal minor of `A` on `insert k T` is `A k k` times the principal minor of the
Schur complement on `T`. -/
lemma det_schur (A : Matrix ι ι ℝ) (k : ι) (hk : A k k ≠ 0) (T : Finset {i // i ≠ k}) :
    (A.submatrix (fun x : (insert k (T.map (Function.Embedding.subtype _)) : Finset ι) => (x : ι))
      (fun x : (insert k (T.map (Function.Embedding.subtype _)) : Finset ι) => (x : ι))).det
      = A k k * ((schur A k).submatrix (fun x : T => (x : {i // i ≠ k}))
          (fun x : T => (x : {i // i ≠ k}))).det := by
  set U : Finset ι := insert k (T.map (Function.Embedding.subtype _)) with hU
  have memU : ∀ t : T, (t.1.1 : ι) ∈ U := fun t =>
    Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ t.2)
  let e : Unit ⊕ T ≃ U :=
    { toFun := fun s => match s with
        | Sum.inl _ => ⟨k, Finset.mem_insert_self _ _⟩
        | Sum.inr t => ⟨t.1.1, memU t⟩
      invFun := fun u => if h : u.1 = k then Sum.inl () else Sum.inr ⟨⟨u.1, h⟩, by
          have hu : (u : ι) ∈ insert k (T.map (Function.Embedding.subtype _)) := u.2
          rcases Finset.mem_insert.1 hu with hu | hu
          · exact absurd hu h
          · obtain ⟨t, ht, he⟩ := Finset.mem_map.1 hu
            have : t = ⟨u.1, h⟩ := Subtype.ext he
            rw [← this]; exact ht⟩
      left_inv := by
        rintro (⟨⟩ | t)
        · simp
        · have : t.1.1 ≠ k := t.1.2
          simp [this]
      right_inv := by
        intro u
        by_cases h : u.1 = k
        · simp only [h, dite_true]; exact Subtype.ext h.symm
        · simp only [h, dite_false] }
  rw [← det_submatrix_equiv_self e]
  let a : Matrix Unit Unit ℝ := Matrix.of fun _ _ => A k k
  let B : Matrix Unit T ℝ := Matrix.of fun _ t => A k t.1.1
  let C : Matrix T Unit ℝ := Matrix.of fun t _ => A t.1.1 k
  let D : Matrix T T ℝ := Matrix.of fun t s => A t.1.1 s.1.1
  have hblk : (A.submatrix (fun x : U => (x : ι)) (fun x : U => (x : ι))).submatrix e e =
      fromBlocks a B C D := by
    ext (⟨⟩ | t) (⟨⟩ | s) <;> rfl
  rw [hblk]
  let ai : Matrix Unit Unit ℝ := Matrix.of fun _ _ => (A k k)⁻¹
  letI hinv : Invertible a :=
    { invOf := ai
      invOf_mul_self := by ext ⟨⟩ ⟨⟩; simp [a, ai, Matrix.mul_apply, hk]
      mul_invOf_self := by ext ⟨⟩ ⟨⟩; simp [a, ai, Matrix.mul_apply, hk] }
  rw [det_fromBlocks₁₁]
  have hai : ⅟a = ai := rfl
  rw [hai, Matrix.det_unique]
  congr 1
  congr 1
  ext t s
  simp [a, ai, B, C, D, schur, Matrix.mul_apply, Matrix.sub_apply]
  field_simp

lemma card_ne (k : ι) : Fintype.card {i // i ≠ k} = Fintype.card ι - 1 := by simp

lemma pivot_pos (A : Matrix ι ι ℝ) (hA : IsPMatrix A) (k : ι) : 0 < A k k := by
  have := hA {k} ⟨k, Finset.mem_singleton_self k⟩
  rwa [Matrix.det_unique] at this

lemma schur_ZP (A : Matrix ι ι ℝ) (hA : IsZPMatrix A) (k : ι) : IsZPMatrix (schur A k) := by
  have ha := pivot_pos A hA.2 k
  refine ⟨?_, ?_⟩
  · intro i j hij
    have h1 : A i j ≤ 0 := hA.1 i j (fun e => hij (Subtype.ext e))
    have h2 : A i k ≤ 0 := hA.1 i k i.2
    have h3 : A k j ≤ 0 := hA.1 k j (fun e => j.2 e.symm)
    have : 0 ≤ A i k * A k j / A k k := div_nonneg (mul_nonneg_of_nonpos_of_nonpos h2 h3) ha.le
    simp only [schur]; linarith
  · intro T hT
    have hU := hA.2 (insert k (T.map (Function.Embedding.subtype _))) ⟨k, Finset.mem_insert_self _ _⟩
    rw [det_schur A k ha.ne'] at hU
    exact pos_of_mul_pos_right hU ha.le

theorem mono : ∀ (n : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ A : Matrix ι ι ℝ, IsZPMatrix A → ∀ x : ι → ℝ, (∀ i, 0 ≤ (A *ᵥ x) i) → ∀ i, 0 ≤ x i := by
  intro n
  induction n with
  | zero =>
    intro ι _ _ hc A _ x _ i
    exact ((Fintype.card_eq_zero_iff.1 hc).false i).elim
  | succ n ih =>
    intro ι _ _ hc A hA x hx
    have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨k⟩ := hne
    have ha := pivot_pos A hA.2 k
    set x' : {i // i ≠ k} → ℝ := fun i => x i.1
    have hrow : ∀ i : ι, (A *ᵥ x) i = A i k * x k + ∑ j : {j // j ≠ k}, A i j.1 * x' j := by
      intro i; simp only [mulVec, dotProduct]; rw [sum_split _ k]
    have hS : ∀ i : {i // i ≠ k}, 0 ≤ (schur A k *ᵥ x') i := by
      intro i
      have e : (schur A k *ᵥ x') i = (A *ᵥ x) i.1 - A i.1 k / A k k * (A *ᵥ x) k := by
        rw [hrow i.1, hrow k]
        simp only [mulVec, dotProduct, schur, sub_mul, Finset.sum_sub_distrib]
        rw [mul_add, Finset.mul_sum]
        field_simp
        ring_nf
        congr 1
        · apply Finset.sum_congr rfl; intro j _; ring
      rw [e]
      have h1 := hx i.1
      have h2 := hx k
      have h3 : A i.1 k ≤ 0 := hA.1 i.1 k i.2
      have : A i.1 k / A k k * (A *ᵥ x) k ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg h3 ha.le) h2
      linarith
    have hx' := ih (by rw [card_ne, hc]; rfl) (schur A k) (schur_ZP A hA k) x' hS
    intro i
    by_cases hik : i = k
    · subst hik
      have h := hx i
      rw [hrow i] at h
      have : ∑ j : {j // j ≠ i}, A i j.1 * x' j ≤ 0 :=
        Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonpos_of_nonneg
          (hA.1 i j.1 (fun e => j.2 e.symm)) (hx' j))
      by_contra hneg
      push Not at hneg
      have : A i i * x i < 0 := mul_neg_of_pos_of_neg ha hneg
      linarith
    · exact hx' ⟨i, hik⟩


lemma det_schur_full (A : Matrix ι ι ℝ) (k : ι) (hk : A k k ≠ 0) :
    A.det = A k k * (schur A k).det := by
  let e : Unit ⊕ {i // i ≠ k} ≃ ι :=
    { toFun := fun s => match s with
        | Sum.inl _ => k
        | Sum.inr t => t.1
      invFun := fun u => if h : u = k then Sum.inl () else Sum.inr ⟨u, h⟩
      left_inv := by
        rintro (⟨⟩ | t)
        · simp
        · have : t.1 ≠ k := t.2
          simp [this]
      right_inv := by
        intro u
        by_cases h : u = k
        · simp only [h, dite_true]
        · simp only [h, dite_false] }
  rw [← det_submatrix_equiv_self e]
  let a : Matrix Unit Unit ℝ := Matrix.of fun _ _ => A k k
  let B : Matrix Unit {i // i ≠ k} ℝ := Matrix.of fun _ t => A k t.1
  let C : Matrix {i // i ≠ k} Unit ℝ := Matrix.of fun t _ => A t.1 k
  let D : Matrix {i // i ≠ k} {i // i ≠ k} ℝ := Matrix.of fun t s => A t.1 s.1
  have hblk : A.submatrix e e = fromBlocks a B C D := by
    ext (⟨⟩ | t) (⟨⟩ | s) <;> rfl
  rw [hblk]
  let ai : Matrix Unit Unit ℝ := Matrix.of fun _ _ => (A k k)⁻¹
  letI hinv : Invertible a :=
    { invOf := ai
      invOf_mul_self := by ext ⟨⟩ ⟨⟩; simp [a, ai, Matrix.mul_apply, hk]
      mul_invOf_self := by ext ⟨⟩ ⟨⟩; simp [a, ai, Matrix.mul_apply, hk] }
  rw [det_fromBlocks₁₁]
  have hai : ⅟a = ai := rfl
  rw [hai, Matrix.det_unique]
  congr 1
  congr 1
  ext t s
  simp [ai, B, C, D, schur, Matrix.mul_apply, Matrix.sub_apply]
  field_simp

/-- A Z-matrix with a positive vector mapped to a positive vector has positive determinant. -/
theorem det_pos : ∀ (n : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ A : Matrix ι ι ℝ, IsZMatrix A → ∀ x : ι → ℝ, (∀ i, 0 < x i) →
      (∀ i, 0 < (A *ᵥ x) i) → 0 < A.det := by
  intro n
  induction n with
  | zero =>
    intro ι _ _ hc A _ x _ _
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.1 hc
    rw [Matrix.det_isEmpty]; exact one_pos
  | succ n ih =>
    intro ι _ _ hc A hZ x hx hAx
    have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨k⟩ := hne
    have hrow : ∀ i : ι, (A *ᵥ x) i = A i k * x k + ∑ j : {j // j ≠ k}, A i j.1 * x j.1 := by
      intro i; simp only [mulVec, dotProduct]; rw [sum_split _ k]
    have ha : 0 < A k k := by
      have h := hAx k
      rw [hrow k] at h
      have : ∑ j : {j // j ≠ k}, A k j.1 * x j.1 ≤ 0 :=
        Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonpos_of_nonneg
          (hZ k j.1 (fun e => j.2 e.symm)) (hx j.1).le)
      by_contra hneg
      push Not at hneg
      have : A k k * x k ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg (hx k).le
      linarith
    set x' : {i // i ≠ k} → ℝ := fun i => x i.1
    have hSZ : IsZMatrix (schur A k) := by
      intro i j hij
      have h1 : A i j ≤ 0 := hZ i j (fun e => hij (Subtype.ext e))
      have h2 : A i k ≤ 0 := hZ i k i.2
      have h3 : A k j ≤ 0 := hZ k j (fun e => j.2 e.symm)
      have : 0 ≤ A i k * A k j / A k k := div_nonneg (mul_nonneg_of_nonpos_of_nonpos h2 h3) ha.le
      simp only [schur]; linarith
    have hS : ∀ i : {i // i ≠ k}, 0 < (schur A k *ᵥ x') i := by
      intro i
      have e : (schur A k *ᵥ x') i = (A *ᵥ x) i.1 - A i.1 k / A k k * (A *ᵥ x) k := by
        rw [hrow i.1, hrow k]
        simp only [mulVec, dotProduct, schur, sub_mul, Finset.sum_sub_distrib]
        rw [mul_add, Finset.mul_sum]
        field_simp
        ring_nf
        congr 1
        · apply Finset.sum_congr rfl; intro j _; ring
      rw [e]
      have h1 := hAx i.1
      have h2 := hAx k
      have h3 : A i.1 k ≤ 0 := hZ i.1 k i.2
      have : A i.1 k / A k k * (A *ᵥ x) k ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg h3 ha.le) h2.le
      linarith
    have hd := ih (by rw [card_ne, hc]; rfl) (schur A k) hSZ x' (fun i => hx i.1) hS
    rw [det_schur_full A k ha.ne']
    exact mul_pos ha hd

/-- Characterization: a Z-matrix with a positive vector mapped to a positive vector is ZP. -/
theorem ZP_of_pos (A : Matrix ι ι ℝ) (hZ : IsZMatrix A) (x : ι → ℝ) (hx : ∀ i, 0 < x i)
    (hAx : ∀ i, 0 < (A *ᵥ x) i) : IsZPMatrix A := by
  refine ⟨hZ, fun S _ => ?_⟩
  apply det_pos (Fintype.card S) rfl (A.submatrix (fun x : S => (x : ι)) (fun x : S => (x : ι)))
    (fun i j hij => hZ i j (fun e => hij (Subtype.ext e))) (fun i : S => x i) (fun i => hx i)
  intro i
  have h := hAx i
  simp only [mulVec, dotProduct] at h ⊢
  have hsplit : ∑ j, A i j * x j = ∑ j : S, A i j * x j + ∑ j ∈ (S : Finset ι)ᶜ, A i j * x j := by
    rw [← Finset.sum_add_sum_compl S, Finset.sum_coe_sort S (fun j => A i j * x j)]
  have hc : ∑ j ∈ (S : Finset ι)ᶜ, A i j * x j ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    have hji : (i : ι) ≠ j := fun e => (Finset.mem_compl.1 hj) (e ▸ i.2)
    exact mul_nonpos_of_nonpos_of_nonneg (hZ i j hji) (hx j).le
  simp only [submatrix_apply]
  linarith

theorem inv_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : IsZPMatrix A) (_hB : IsZMatrix B) (_hAB : ∀ l m, A l m ≤ B l m) :
    IsUnit A.det ∧ ∀ l m, 0 ≤ A⁻¹ l m := by
  have hdet : IsUnit A.det := by
    rcases isEmpty_or_nonempty n with hn | hn
    · rw [Matrix.det_isEmpty]; exact isUnit_one
    · obtain ⟨k⟩ := hn
      have h := hA.2 Finset.univ ⟨k, Finset.mem_univ k⟩
      have e : A.submatrix (fun x : (Finset.univ : Finset n) => (x : n))
          (fun x : (Finset.univ : Finset n) => (x : n)) =
          (A.submatrix (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x))
            (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x))) := rfl
      rw [e, Matrix.det_submatrix_equiv_self] at h
      exact (ne_of_gt h).isUnit
  refine ⟨hdet, fun l m => ?_⟩
  have hm := mono _ rfl A hA (A⁻¹ *ᵥ Pi.single m 1) (by
    intro i
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
    by_cases h : i = m
    · subst h; simp
    · simp [h]) l
  simpa [Matrix.mulVec_single_one] using hm


theorem b1c {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : IsZPMatrix A) (hB : IsZMatrix B) (hAB : ∀ l m, A l m ≤ B l m) :
    IsZPMatrix (A * B⁻¹) ∧ IsZPMatrix (B⁻¹ * A) := by
  obtain ⟨hAu, hAinv⟩ := inv_nonneg A A hA hA.1 (fun _ _ => le_rfl)
  -- positive vector for A
  set y : n → ℝ := A⁻¹ *ᵥ (fun _ => 1) with hy
  have hAy : A *ᵥ y = fun _ => 1 := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hAu, Matrix.one_mulVec]
  have rowpos : ∀ (M : Matrix n n ℝ), IsUnit M.det → (∀ l m, 0 ≤ M⁻¹ l m) →
      ∀ v : n → ℝ, (∀ i, 0 < v i) → ∀ i, 0 < (M⁻¹ *ᵥ v) i := by
    intro M hM hMi v hv i
    simp only [mulVec, dotProduct]
    apply Finset.sum_pos' (fun j _ => mul_nonneg (hMi i j) (hv j).le)
    by_contra hall
    push Not at hall
    have hz : ∀ j, M⁻¹ i j = 0 := fun j => by
      have h1 := hall j (Finset.mem_univ j)
      have h2 := mul_nonneg (hMi i j) (hv j).le
      have h3 : M⁻¹ i j * v j = 0 := le_antisymm h1 h2
      rcases mul_eq_zero.1 h3 with h | h
      · exact h
      · exact absurd h (hv j).ne'
    have : (M⁻¹ * M) i i = 0 := by simp [Matrix.mul_apply, hz]
    rw [Matrix.nonsing_inv_mul M hM, Matrix.one_apply_eq] at this
    exact one_ne_zero this
  have hypos : ∀ i, 0 < y i := rowpos A hAu hAinv _ (fun _ => one_pos)
  have hAypos : ∀ i, 0 < (A *ᵥ y) i := by rw [hAy]; intro; exact one_pos
  have hBy : ∀ i, 0 < (B *ᵥ y) i := by
    intro i
    have : (A *ᵥ y) i ≤ (B *ᵥ y) i := by
      simp only [mulVec, dotProduct]
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hAB i j) (hypos j).le)
    linarith [hAypos i]
  have hBZP : IsZPMatrix B := ZP_of_pos B hB y hypos hBy
  obtain ⟨hBu, hBinv⟩ := inv_nonneg B B hBZP hB (fun _ _ => le_rfl)
  have hdiff : ∀ l m, 0 ≤ (B - A) l m := fun l m => by simp [hAB l m]
  refine ⟨?_, ?_⟩
  · -- A B⁻¹ = 1 - (B - A) B⁻¹
    have he : A * B⁻¹ = 1 - (B - A) * B⁻¹ := by
      rw [Matrix.sub_mul, Matrix.mul_nonsing_inv B hBu]; abel
    have hZ : IsZMatrix (A * B⁻¹) := by
      intro l m hlm
      rw [he, Matrix.sub_apply, Matrix.one_apply_ne hlm]
      have : 0 ≤ ((B - A) * B⁻¹) l m :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (hdiff l j) (hBinv j m))
      linarith
    refine ZP_of_pos _ hZ (B *ᵥ y) hBy ?_
    have : (A * B⁻¹) *ᵥ (B *ᵥ y) = A *ᵥ y := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul B hBu, Matrix.mul_one]
    rw [this]
    exact hAypos
  · have he : B⁻¹ * A = 1 - B⁻¹ * (B - A) := by
      rw [Matrix.mul_sub, Matrix.nonsing_inv_mul B hBu]; abel
    have hZ : IsZMatrix (B⁻¹ * A) := by
      intro l m hlm
      rw [he, Matrix.sub_apply, Matrix.one_apply_ne hlm]
      have : 0 ≤ (B⁻¹ * (B - A)) l m :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (hBinv l j) (hdiff j m))
      linarith
    refine ZP_of_pos _ hZ y hypos ?_
    rw [← Matrix.mulVec_mulVec]
    exact rowpos B hBu hBinv _ hAypos

theorem b1g {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) (hQ : ∀ l m, 0 ≤ Q l m) (hA : IsZPMatrix (1 - Q)) :
    spectralRadius ℂ (Q.map (algebraMap ℝ ℂ)) < 1 := by
  set Qc := Q.map (algebraMap ℝ ℂ) with hQc
  have hfin : (spectrum ℂ Qc).Finite :=
    (Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic Qc).ne_zero).subset
      (fun r hr => Matrix.mem_spectrum_iff_isRoot_charpoly.1 hr)
  have key : ∀ r ∈ spectrum ℂ Qc, ‖r‖ < 1 := by
    intro r hr
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hr
    obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hr
    have hQz : ∀ i, (Qc *ᵥ z) i = r * z i := by
      intro i
      have := congrFun hz i
      rw [Matrix.sub_mulVec, Matrix.algebraMap_eq_diagonal, Pi.sub_apply,
        Matrix.mulVec_diagonal] at this
      simp only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Pi.zero_apply] at this
      linear_combination -this
    by_contra hge
    push Not at hge
    set w : n → ℝ := fun i => ‖z i‖ with hwdef
    have hw : ∀ i, ‖r‖ * w i ≤ (Q *ᵥ w) i := by
      intro i
      calc ‖r‖ * w i = ‖r * z i‖ := by simp [hwdef, norm_mul]
        _ = ‖(Qc *ᵥ z) i‖ := by rw [hQz]
        _ = ‖∑ j, (Q i j : ℂ) * z j‖ := by simp [hQc, Matrix.mulVec, dotProduct]
        _ ≤ ∑ j, ‖(Q i j : ℂ) * z j‖ := norm_sum_le _ _
        _ = ∑ j, Q i j * w j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hQ i j)]
        _ = (Q *ᵥ w) i := rfl
    have hneg : ∀ i, 0 ≤ ((1 - Q) *ᵥ (-w)) i := by
      intro i
      rw [Matrix.mulVec_neg, Matrix.sub_mulVec, Matrix.one_mulVec]
      simp only [Pi.neg_apply, Pi.sub_apply]
      have h1 := hw i
      have h2 : 0 ≤ w i := norm_nonneg _
      nlinarith
    have hle := mono _ rfl (1 - Q) hA (-w) hneg
    apply hz0
    funext i
    have h1 := hle i
    simp only [Pi.neg_apply, neg_nonneg] at h1
    have h2 : ‖z i‖ = 0 := le_antisymm h1 (norm_nonneg _)
    simpa using h2
  unfold spectralRadius
  rw [← hfin.coe_toFinset]
  simp only [Finset.mem_coe]
  rw [← Finset.sup_eq_iSup, Finset.sup_lt_iff (by simp)]
  intro r hr
  rw [Set.Finite.mem_toFinset] at hr
  have := key r hr
  exact_mod_cast (show ‖r‖₊ < 1 from this)

end PRB1

namespace PRB1
open PriceRobust.Stability

lemma split_sum' {n : Type*} [Fintype n] [DecidableEq n] (S : Finset n) (f : n → ℝ) :
    ∑ l : {l // l ∈ S}, f l + ∑ l : {l // l ∉ S}, f l = ∑ l, f l := by
  rw [← Finset.sum_add_sum_compl S f, Finset.sum_coe_sort S f]
  congr 1
  exact (Finset.sum_subtype Sᶜ (fun x => by simp) f).symm

theorem det_pos_of_pd {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)) : 0 < A.det := by
  set f : ℝ → ℝ := fun t => ((1 - t) • (1 : Matrix ι ι ℝ) + t • A).det with hf
  have hcont : Continuous f := by
    apply Continuous.matrix_det
    fun_prop
  have hne : ∀ t ∈ Set.Icc (0:ℝ) 1, f t ≠ 0 := by
    intro t ht h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have e : x ⬝ᵥ (((1 - t) • (1 : Matrix ι ι ℝ) + t • A) *ᵥ x) =
        (1 - t) * (x ⬝ᵥ x) + t * (x ⬝ᵥ (A *ᵥ x)) := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    rw [hx, dotProduct_zero] at e
    have hxx : 0 < x ⬝ᵥ x := by
      have h1 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
      have h2 : x ⬝ᵥ x ≠ 0 := fun h => hx0 (dotProduct_self_eq_zero.1 h)
      exact lt_of_le_of_ne h1 (Ne.symm h2)
    have hxA := hA x hx0
    rcases ht with ⟨ht0, ht1⟩
    rcases eq_or_lt_of_le ht0 with h | h
    · subst h; simp at e; linarith
    · have : 0 < t * (x ⬝ᵥ (A *ᵥ x)) := mul_pos h hxA
      have : 0 ≤ (1 - t) * (x ⬝ᵥ x) := mul_nonneg (by linarith) hxx.le
      linarith
  by_contra hle
  push Not at hle
  have f0 : f 0 = 1 := by simp [hf]
  have f1 : f 1 = A.det := by simp [hf]
  have hivt := intermediate_value_Icc' (show (0:ℝ) ≤ 1 by norm_num) hcont.continuousOn
  have : (0:ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨by rw [f1]; exact hle, by rw [f0]; norm_num⟩
  obtain ⟨t, ht, hft⟩ := hivt this
  exact hne t ht hft

theorem ZP_of_pd {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (hZ : IsZMatrix A)
    (hA : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)) : IsZPMatrix A := by
  refine ⟨hZ, fun S _ => ?_⟩
  apply det_pos_of_pd
  intro x hx
  set y : ι → ℝ := fun l => if h : l ∈ S then x ⟨l, h⟩ else 0 with hy
  have hysum : ∀ g : ι → ℝ, ∑ l, y l * g l = ∑ s : S, x s * g s := by
    intro g
    rw [← split_sum' S]
    have h0 : ∑ l : {l // l ∉ S}, y l * g l = 0 :=
      Finset.sum_eq_zero (fun l _ => by simp [hy, l.2])
    rw [h0, add_zero]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp [hy, s.2]
  have hy0 : y ≠ 0 := by
    intro h
    apply hx
    funext s
    have := congrFun h s.1
    simpa [hy, s.2] using this
  have key := hA y hy0
  have e : y ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ ((A.submatrix (fun x : S => (x : ι)) (fun x : S => (x : ι))) *ᵥ x) := by
    simp only [dotProduct, mulVec]
    rw [hysum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    congr 1
    have := hysum (fun m => A s m)
    simp only [submatrix_apply]
    rw [show (∑ m, A s m * y m) = ∑ m, y m * A s m from Finset.sum_congr rfl (fun _ _ => mul_comm _ _),
      this]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [← e]; exact key

end PRB1

namespace PRSLCP
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_toLp (f : ι → ℝ) :
    ‖(WithLp.toLp 2 f : EuclideanSpace ℝ ι)‖ = Real.sqrt (f ⬝ᵥ f) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, sq]

theorem dist_toLp (f g : ι → ℝ) :
    dist (WithLp.toLp 2 f : EuclideanSpace ℝ ι) (WithLp.toLp 2 g) =
      Real.sqrt ((f - g) ⬝ᵥ (f - g)) := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  simp [dotProduct, Real.dist_eq, sq_abs, sq]

theorem self_dot_nonneg (f : ι → ℝ) : 0 ≤ f ⬝ᵥ f :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

/-- Strong monotonicity of a positive definite matrix. -/
theorem pd_coercive (A : Matrix ι ι ℝ) (hA : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)) :
    ∃ m : ℝ, 0 < m ∧ ∀ d : ι → ℝ, m * (d ⬝ᵥ d) ≤ d ⬝ᵥ (A *ᵥ d) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, one_pos, fun d => ?_⟩
    simp [dotProduct]
  obtain ⟨i0⟩ := hι
  set S : Set (EuclideanSpace ℝ ι) := Metric.sphere 0 1
  have hSne : S.Nonempty := by
    refine ⟨EuclideanSpace.single i0 1, ?_⟩
    simp [S]
  set g : EuclideanSpace ℝ ι → ℝ := fun x => (WithLp.ofLp x) ⬝ᵥ (A *ᵥ WithLp.ofLp x)
  have hg : Continuous g := by
    have h1 : Continuous (fun x : EuclideanSpace ℝ ι => WithLp.ofLp x) := PiLp.continuous_ofLp 2 _
    exact Continuous.dotProduct h1 (Continuous.matrix_mulVec continuous_const h1)
  obtain ⟨u, huS, humin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ ι) 1).exists_isMinOn hSne
    hg.continuousOn
  have hu0 : WithLp.ofLp u ≠ 0 := by
    intro h
    have : ‖u‖ = 1 := by simpa [S] using huS
    have h2 : u = 0 := by
      have : u = WithLp.toLp 2 (WithLp.ofLp u) := rfl
      rw [this, h]; rfl
    rw [h2, norm_zero] at this
    exact zero_ne_one this
  refine ⟨g u, hA _ hu0, fun d => ?_⟩
  by_cases hd : d = 0
  · subst hd; simp
  have hdd : 0 < d ⬝ᵥ d := by
    rcases (self_dot_nonneg d).lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.1 h.symm) hd
  set r := Real.sqrt (d ⬝ᵥ d) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hdd
  have hr2 : r ^ 2 = d ⬝ᵥ d := Real.sq_sqrt hdd.le
  have hmem : (WithLp.toLp 2 (r⁻¹ • d) : EuclideanSpace ℝ ι) ∈ S := by
    simp only [S, mem_sphere_zero_iff_norm, norm_toLp, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    rw [← mul_assoc, ← hr2, show r⁻¹ * r⁻¹ * r ^ 2 = 1 by field_simp]
    simp
  have hmin := humin hmem
  simp only [g] at hmin
  change (WithLp.ofLp u) ⬝ᵥ (A *ᵥ WithLp.ofLp u) ≤ (r⁻¹ • d) ⬝ᵥ (A *ᵥ (r⁻¹ • d)) at hmin
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    ← mul_assoc] at hmin
  have : g u * (d ⬝ᵥ d) ≤ r⁻¹ * r⁻¹ * (d ⬝ᵥ (A *ᵥ d)) * r ^ 2 := by
    rw [← hr2]; exact mul_le_mul_of_nonneg_right hmin (sq_nonneg r)
  calc g u * (d ⬝ᵥ d) ≤ r⁻¹ * r⁻¹ * (d ⬝ᵥ (A *ᵥ d)) * r ^ 2 := this
    _ = d ⬝ᵥ (A *ᵥ d) := by field_simp

/-- Lipschitz bound of a matrix in the Euclidean square norm. -/
theorem mulVec_sq_le (A : Matrix ι ι ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ d : ι → ℝ, (A *ᵥ d) ⬝ᵥ (A *ᵥ d) ≤ L * (d ⬝ᵥ d) := by
  refine ⟨∑ l, ∑ m, A l m ^ 2 + 1, by positivity, fun d => ?_⟩
  have hrow : ∀ l, (A *ᵥ d) l * (A *ᵥ d) l ≤ (∑ m, A l m ^ 2) * (d ⬝ᵥ d) := by
    intro l
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun m => A l m) d
    have e : d ⬝ᵥ d = ∑ m, d m ^ 2 := by simp [dotProduct, sq]
    rw [e, ← sq]; simpa [mulVec, dotProduct] using this
  calc (A *ᵥ d) ⬝ᵥ (A *ᵥ d) = ∑ l, (A *ᵥ d) l * (A *ᵥ d) l := rfl
    _ ≤ ∑ l, (∑ m, A l m ^ 2) * (d ⬝ᵥ d) := Finset.sum_le_sum (fun l _ => hrow l)
    _ = (∑ l, ∑ m, A l m ^ 2) * (d ⬝ᵥ d) := by rw [Finset.sum_mul]
    _ ≤ (∑ l, ∑ m, A l m ^ 2 + 1) * (d ⬝ᵥ d) := by
        nlinarith [self_dot_nonneg d]

/-- Existence for the linear complementarity problem with a positive definite matrix,
via the projected fixed-point map `z ↦ max(0, z - τ (c + A z))`, a contraction. -/
theorem lcp_exists (A : Matrix ι ι ℝ) (hA : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x))
    (c : ι → ℝ) :
    ∃ z : ι → ℝ, 0 ≤ z ∧ 0 ≤ c + A *ᵥ z ∧ z ⬝ᵥ (c + A *ᵥ z) = 0 := by
  obtain ⟨m, hm, hmd⟩ := pd_coercive A hA
  obtain ⟨L, hL, hLd⟩ := mulVec_sq_le A
  set τ : ℝ := m / L with hτ
  have hτ0 : 0 < τ := div_pos hm hL
  set κ : ℝ := max (1 - m ^ 2 / L) 0 with hκ
  have hκ1 : κ < 1 := by
    rw [hκ]; apply max_lt _ one_pos
    have : 0 < m ^ 2 / L := by positivity
    linarith
  have hκ0 : 0 ≤ κ := le_max_right _ _
  set G0 : (ι → ℝ) → (ι → ℝ) := fun z l => max (z l - τ * (c + A *ᵥ z) l) 0 with hG0
  set G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
    fun x => WithLp.toLp 2 (G0 (WithLp.ofLp x)) with hG
  have hcontr : ∀ z z' : ι → ℝ, (G0 z - G0 z') ⬝ᵥ (G0 z - G0 z') ≤ κ * ((z - z') ⬝ᵥ (z - z')) := by
    intro z z'
    set d := z - z' with hd
    have h1 : (G0 z - G0 z') ⬝ᵥ (G0 z - G0 z') ≤ (d - τ • (A *ᵥ d)) ⬝ᵥ (d - τ • (A *ᵥ d)) := by
      simp only [dotProduct]
      apply Finset.sum_le_sum
      intro l _
      have hl : (d - τ • (A *ᵥ d)) l = (z l - τ * (c + A *ᵥ z) l) - (z' l - τ * (c + A *ᵥ z') l) := by
        simp only [hd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_sub, Pi.add_apply]
        ring
      rw [hl]
      simp only [Pi.sub_apply, hG0]
      rw [← sq, ← sq, ← sq_abs, ← sq_abs (_ - _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_max_sub_max_le_abs _ _ _) 2
    have h2 : (d - τ • (A *ᵥ d)) ⬝ᵥ (d - τ • (A *ᵥ d)) =
        d ⬝ᵥ d - 2 * τ * (d ⬝ᵥ (A *ᵥ d)) + τ ^ 2 * ((A *ᵥ d) ⬝ᵥ (A *ᵥ d)) := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        dotProduct_comm (A *ᵥ d) d]
      ring
    have h3 := hmd d
    have h4 := hLd d
    have hdd := self_dot_nonneg d
    have h5 : d ⬝ᵥ d - 2 * τ * (d ⬝ᵥ (A *ᵥ d)) + τ ^ 2 * ((A *ᵥ d) ⬝ᵥ (A *ᵥ d)) ≤
        (1 - m ^ 2 / L) * (d ⬝ᵥ d) := by
      have e1 : 2 * τ * (m * (d ⬝ᵥ d)) ≤ 2 * τ * (d ⬝ᵥ (A *ᵥ d)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have e2 : τ ^ 2 * ((A *ᵥ d) ⬝ᵥ (A *ᵥ d)) ≤ τ ^ 2 * (L * (d ⬝ᵥ d)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      have e3 : (1 - m ^ 2 / L) * (d ⬝ᵥ d) = d ⬝ᵥ d - 2 * τ * (m * (d ⬝ᵥ d)) + τ ^ 2 * (L * (d ⬝ᵥ d)) := by
        rw [hτ]; field_simp; ring
      linarith
    have h6 : (1 - m ^ 2 / L) * (d ⬝ᵥ d) ≤ κ * (d ⬝ᵥ d) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hdd
    linarith
  set K : NNReal := Real.toNNReal (Real.sqrt κ) with hK
  have hKc : (K : ℝ) = Real.sqrt κ := Real.coe_toNNReal _ (Real.sqrt_nonneg _)
  have hK1 : K < 1 := by
    rw [← NNReal.coe_lt_coe, hKc, NNReal.coe_one, Real.sqrt_lt' one_pos]; simpa using hκ1
  have hGc : ContractingWith K G := by
    refine ⟨hK1, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
    simp only [hG, dist_toLp]
    rw [show dist x y = dist (WithLp.toLp 2 (WithLp.ofLp x) : EuclideanSpace ℝ ι)
      (WithLp.toLp 2 (WithLp.ofLp y)) from rfl, dist_toLp, hKc,
      ← Real.sqrt_mul hκ0]
    exact Real.sqrt_le_sqrt (hcontr _ _)
  set zE := ContractingWith.fixedPoint G hGc
  have hfix : G zE = zE := ContractingWith.fixedPoint_isFixedPt hGc
  set z := WithLp.ofLp zE with hz
  have hfz : G0 z = z := by
    have := congrArg WithLp.ofLp hfix
    simpa [hG] using this
  have hzl : ∀ l, max (z l - τ * (c + A *ᵥ z) l) 0 = z l := fun l => congrFun hfz l
  have hz0 : 0 ≤ z := fun l => by rw [← hzl l]; exact le_max_right _ _
  have hQ0 : 0 ≤ c + A *ᵥ z := by
    intro l
    have h := hzl l
    by_contra hneg
    push Not at hneg
    have : z l < z l - τ * (c + A *ᵥ z) l := by
      have : 0 < τ * -(c + A *ᵥ z) l := mul_pos hτ0 (neg_pos.mpr hneg)
      linarith
    have : z l - τ * (c + A *ᵥ z) l ≤ max (z l - τ * (c + A *ᵥ z) l) 0 := le_max_left _ _
    rw [h] at this
    linarith
  refine ⟨z, hz0, hQ0, ?_⟩
  apply Finset.sum_eq_zero
  intro l _
  have h := hzl l
  rcases (hz0 l).lt_or_eq with hpos | hzero
  · have : max (z l - τ * (c + A *ᵥ z) l) 0 = z l - τ * (c + A *ᵥ z) l := by
      rcases le_total (z l - τ * (c + A *ᵥ z) l) 0 with h' | h'
      · rw [max_eq_right h'] at h; simp at hpos; linarith
      · exact max_eq_left h'
    rw [this] at h
    have : τ * (c + A *ᵥ z) l = 0 := by linarith
    rcases mul_eq_zero.1 this with h'' | h''
    · exact absurd h'' hτ0.ne'
    · rw [h'', mul_zero]
  · rw [← hzero]; simp

end PRSLCP

namespace PRSBlock
open Matrix PriceRobust.Stability

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Comparison principle for the LCP with a positive definite Z-matrix: a solution is
below every feasible point. -/
theorem lcp_le (B : Matrix n n ℝ) (hZ : IsZMatrix B)
    (hPD : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (B *ᵥ x))
    (q l l' : n → ℝ) (hl : 0 ≤ l) (hq : 0 ≤ q + B *ᵥ l) (hc : l ⬝ᵥ (q + B *ᵥ l) = 0)
    (hl' : 0 ≤ l') (hq' : 0 ≤ q + B *ᵥ l') : l ≤ l' := by
  have hterm : ∀ k, l k * (q + B *ᵥ l) k = 0 := by
    have hnn : ∀ k ∈ Finset.univ, 0 ≤ l k * (q + B *ᵥ l) k :=
      fun k _ => mul_nonneg (hl k) (hq k)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hc
    exact fun k => this k (Finset.mem_univ k)
  set e : n → ℝ := fun k => max (l k - l' k) 0 with he
  set f : n → ℝ := fun k => max (l' k - l k) 0 with hf
  have hlef : l - l' = e - f := by
    funext k
    simp only [he, hf, Pi.sub_apply]
    rcases le_total (l k) (l' k) with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have h1 : e ⬝ᵥ (q + B *ᵥ l) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rcases (le_max_right (l k - l' k) 0).lt_or_eq with h | h
    · have hlk : 0 < l k := by
        have := hl' k; simp only [Pi.zero_apply] at this
        have : l k - l' k > 0 := by
          by_contra hh; push Not at hh
          have : max (l k - l' k) 0 = 0 := max_eq_right hh
          linarith
        linarith
      have := hterm k
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · rw [h', mul_zero]
    · have : e k = 0 := h.symm
      rw [this, zero_mul]
  have h2 : 0 ≤ e ⬝ᵥ (q + B *ᵥ l') :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (le_max_right _ _) (hq' k))
  have h3 : e ⬝ᵥ (B *ᵥ f) ≤ 0 := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_nonpos
    intro k _
    apply Finset.sum_nonpos
    intro j _
    by_cases hkj : k = j
    · subst hkj
      have : e k * f k = 0 := by
        simp only [he, hf]
        rcases le_total (l k) (l' k) with h | h
        · rw [max_eq_right (by linarith)]; ring
        · rw [max_eq_right (show l' k - l k ≤ 0 by linarith)]; ring
      calc e k * (B k k * f k) = B k k * (e k * f k) := by ring
        _ = 0 := by rw [this, mul_zero]
        _ ≤ 0 := le_rfl
    · have := hZ k j hkj
      have h4 : 0 ≤ e k * f j := mul_nonneg (le_max_right _ _) (le_max_right _ _)
      nlinarith
  have h4 : e ⬝ᵥ (B *ᵥ e) ≤ 0 := by
    have e5 : e ⬝ᵥ (B *ᵥ (l - l')) = e ⬝ᵥ (q + B *ᵥ l) - e ⬝ᵥ (q + B *ᵥ l') := by
      rw [Matrix.mulVec_sub, ← dotProduct_sub]; congr 1; abel
    rw [hlef, Matrix.mulVec_sub, dotProduct_sub] at e5
    linarith
  have he0 : e = 0 := by
    by_contra h
    linarith [hPD e h]
  intro k
  have := congrFun he0 k
  simp only [he, Pi.zero_apply] at this
  have := le_max_left (l k - l' k) 0
  linarith

/-- The objective of the block problem: `(x - w)ᵀ (α - B x)`. -/
def obj (B : Matrix n n ℝ) (w α x : n → ℝ) : ℝ := (x - w) ⬝ᵥ (α - B *ᵥ x)

theorem dot_symm (B : Matrix n n ℝ) (hS : Bᵀ = B) (u v : n → ℝ) :
    u ⬝ᵥ (B *ᵥ v) = v ⬝ᵥ (B *ᵥ u) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS, dotProduct_comm]

/-- KKT sufficiency: from an LCP solution, the explicit point is feasible and is a strict
maximizer with a quadratic gap. -/
theorem kkt (B : Matrix n n ℝ) (hS : Bᵀ = B) (hZ : IsZMatrix B)
    (hPD : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (B *ᵥ x))
    (hBu : IsUnit B.det) (hBinv : ∀ l m, 0 ≤ B⁻¹ l m)
    (w α : n → ℝ) (hw : 0 ≤ w) (hα : 0 ≤ α)
    (lam : n → ℝ) (hl : 0 ≤ lam) (hq : 0 ≤ (α - B *ᵥ w) + B *ᵥ lam)
    (hc : lam ⬝ᵥ ((α - B *ᵥ w) + B *ᵥ lam) = 0) :
    let x : n → ℝ := (1/2 : ℝ) • (B⁻¹ *ᵥ α + w - lam)
    0 ≤ x ∧ B *ᵥ x ≤ α ∧
      ∀ x' : n → ℝ, B *ᵥ x' ≤ α → obj B w α x' + (x' - x) ⬝ᵥ (B *ᵥ (x' - x)) ≤ obj B w α x := by
  intro x
  have hBBi : B *ᵥ (B⁻¹ *ᵥ α) = α := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hBu, Matrix.one_mulVec]
  have hBx : B *ᵥ x = (1/2 : ℝ) • (α + B *ᵥ w - B *ᵥ lam) := by
    simp only [x, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_add, hBBi]
  have hc0 : 0 ≤ B⁻¹ *ᵥ α := by
    intro k
    simp only [Pi.zero_apply, mulVec, dotProduct]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hBinv k j) (hα j))
  -- x ≥ 0 via comparison with lam' = B⁻¹ α + w
  have hle := lcp_le B hZ hPD (α - B *ᵥ w) lam (B⁻¹ *ᵥ α + w) hl hq hc
    (by intro k; have := hc0 k; have := hw k; simp only [Pi.zero_apply, Pi.add_apply] at *; linarith)
    (by
      rw [Matrix.mulVec_add, hBBi]
      intro k; have := hα k; simp only [Pi.zero_apply, Pi.add_apply, Pi.sub_apply] at *; linarith)
  refine ⟨?_, ?_, ?_⟩
  · intro k
    have := hle k
    simp only [x, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul] at this ⊢
    linarith
  · intro k
    have := hq k
    rw [hBx]
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul] at this ⊢
    linarith
  · intro x' hx'
    set d := x' - x with hd
    have hx'e : x' = x + d := by rw [hd]; abel
    -- f(x') - f(x) = (B lam)·d - d·B d
    have key : obj B w α x' = obj B w α x + d ⬝ᵥ (B *ᵥ lam) - d ⬝ᵥ (B *ᵥ d) := by
      simp only [obj]
      rw [hx'e]
      have s1 := dot_symm B hS (x - w) d
      have e2 : (2 : ℝ) * (d ⬝ᵥ (B *ᵥ x)) = d ⬝ᵥ α + d ⬝ᵥ (B *ᵥ w) - d ⬝ᵥ (B *ᵥ lam) := by
        rw [hBx, dotProduct_smul, smul_eq_mul, dotProduct_sub, dotProduct_add]; ring
      simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, sub_dotProduct,
        dotProduct_add, dotProduct_sub] at s1 ⊢
      linarith
    have hlBd : d ⬝ᵥ (B *ᵥ lam) ≤ 0 := by
      rw [dot_symm B hS d lam]
      have e3 : lam ⬝ᵥ (B *ᵥ d) = lam ⬝ᵥ (B *ᵥ x' - α) + lam ⬝ᵥ (α - B *ᵥ x) := by
        rw [hd, Matrix.mulVec_sub, ← dotProduct_add]; congr 1; abel
      have e4 : lam ⬝ᵥ (α - B *ᵥ x) = 0 := by
        have : α - B *ᵥ x = (1/2 : ℝ) • ((α - B *ᵥ w) + B *ᵥ lam) := by
          rw [hBx]; funext k
          simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]; ring
        rw [this, dotProduct_smul, hc, smul_zero]
      have e5 : lam ⬝ᵥ (B *ᵥ x' - α) ≤ 0 :=
        Finset.sum_nonpos (fun k _ => mul_nonpos_of_nonneg_of_nonpos (hl k)
          (by have := hx' k; simp only [Pi.sub_apply]; linarith))
      linarith
    linarith

/-- Block form of Lemma 2: if `α̌ ≤ α̂` then the maximizers satisfy
`0 ≤ x̂ - x̌ ≤ B⁻¹ (α̂ - α̌)`. -/
theorem block_lemma2 (B : Matrix n n ℝ) (hS : Bᵀ = B) (hZ : IsZMatrix B)
    (hPD : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (B *ᵥ x))
    (w : n → ℝ) (hw : 0 ≤ w) (α1 α2 : n → ℝ) (hα1 : 0 ≤ α1) (h12 : α1 ≤ α2)
    (x1 x2 : n → ℝ) (hx1 : 0 ≤ x1 ∧ B *ᵥ x1 ≤ α1) (hx2 : 0 ≤ x2 ∧ B *ᵥ x2 ≤ α2)
    (hopt1 : ∀ x, 0 ≤ x → B *ᵥ x ≤ α1 → obj B w α1 x ≤ obj B w α1 x1)
    (hopt2 : ∀ x, 0 ≤ x → B *ᵥ x ≤ α2 → obj B w α2 x ≤ obj B w α2 x2) :
    ∀ k, 0 ≤ x2 k - x1 k ∧ x2 k - x1 k ≤ (B⁻¹ *ᵥ (α2 - α1)) k := by
  have hZP : IsZPMatrix B := PRB1.ZP_of_pd B hZ hPD
  obtain ⟨hBu, hBinv⟩ := PRB1.inv_nonneg B B hZP hZ (fun _ _ => le_rfl)
  have hα2 : 0 ≤ α2 := le_trans hα1 h12
  obtain ⟨l1, hl1, hq1, hc1⟩ := PRSLCP.lcp_exists B hPD (α1 - B *ᵥ w)
  obtain ⟨l2, hl2, hq2, hc2⟩ := PRSLCP.lcp_exists B hPD (α2 - B *ᵥ w)
  -- identify the maximizers with the KKT points
  have ident : ∀ (α l xo : n → ℝ), 0 ≤ α → 0 ≤ l → 0 ≤ (α - B *ᵥ w) + B *ᵥ l →
      l ⬝ᵥ ((α - B *ᵥ w) + B *ᵥ l) = 0 → (0 ≤ xo ∧ B *ᵥ xo ≤ α) →
      (∀ x, 0 ≤ x → B *ᵥ x ≤ α → obj B w α x ≤ obj B w α xo) →
      xo = (1/2 : ℝ) • (B⁻¹ *ᵥ α + w - l) := by
    intro α l xo hα hl hq hc hxo hopt
    obtain ⟨h0, hB, hmax⟩ := kkt B hS hZ hPD hBu hBinv w α hw hα l hl hq hc
    have h1 := hmax xo hxo.2
    have h2 := hopt _ h0 hB
    have h3 : (xo - (1/2 : ℝ) • (B⁻¹ *ᵥ α + w - l)) ⬝ᵥ
        (B *ᵥ (xo - (1/2 : ℝ) • (B⁻¹ *ᵥ α + w - l))) ≤ 0 := by linarith
    by_contra hne
    have := hPD _ (sub_ne_zero.2 hne)
    linarith
  have e1 := ident α1 l1 x1 hα1 hl1 hq1 hc1 hx1 hopt1
  have e2 := ident α2 l2 x2 hα2 hl2 hq2 hc2 hx2 hopt2
  set δ := B⁻¹ *ᵥ (α2 - α1) with hδ
  have hBδ : B *ᵥ δ = α2 - α1 := by
    rw [hδ, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hBu, Matrix.one_mulVec]
  have hδ0 : 0 ≤ δ := by
    intro k
    simp only [hδ, Pi.zero_apply, mulVec, dotProduct]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hBinv k j)
      (by have := h12 j; simp only [Pi.sub_apply]; linarith))
  -- λ₂ ≤ λ₁
  have hA : l2 ≤ l1 := lcp_le B hZ hPD _ l2 l1 hl2 hq2 hc2 hl1 (by
    intro k; have := hq1 k; have := h12 k
    simp only [Pi.zero_apply, Pi.add_apply, Pi.sub_apply] at *; linarith)
  -- λ₁ ≤ λ₂ + δ
  have hB : l1 ≤ l2 + δ := lcp_le B hZ hPD _ l1 (l2 + δ) hl1 hq1 hc1
    (by intro k; have := hl2 k; have := hδ0 k; simp only [Pi.zero_apply, Pi.add_apply] at *; linarith)
    (by
      rw [Matrix.mulVec_add, hBδ]
      intro k; have := hq2 k
      simp only [Pi.zero_apply, Pi.add_apply, Pi.sub_apply] at *; linarith)
  have hdiff : x2 - x1 = (1/2 : ℝ) • (δ + (l1 - l2)) := by
    rw [e1, e2, hδ, Matrix.mulVec_sub]
    funext k
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  intro k
  have hk := congrFun hdiff k
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hk
  have := hA k; have := hB k; have := hδ0 k
  simp only [Pi.add_apply, Pi.zero_apply] at *
  constructor <;> linarith

end PRSBlock

open PriceRobust.Stability Matrix in
theorem solution {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (M : Market ι F) (hM : M.Standing) (w : ι → ℝ) (hw : ∀ l, 0 < w l)
    (phat ptil : ι → ℝ) (hphat : 0 ≤ phat) (hptil : 0 ≤ ptil)
    (qhat qtil qchk : ι → ℝ)
    (hqhat : M.IsRobustBR w phat qhat) (hqtil : M.IsRobustBR w ptil qtil)
    (hqchk : M.IsRobustBR w (fun l => min (phat l) (ptil l)) qchk) (i : F) :
    let pchk : ι → ℝ := fun l => min (phat l) (ptil l)
    let αhat := M.blockAlpha i phat
    let αtil := M.blockAlpha i ptil
    let αchk := M.blockAlpha i pchk
    ∀ (l : ι) (hl : M.firm l = i),
      (0 ≤ qhat l - qchk l ∧
        qhat l - qchk l ≤
          ((M.Rblock i)⁻¹ *ᵥ (fun k : {l // M.firm l = i} => αhat k.1 - αchk k.1)) ⟨l, hl⟩) ∧
      (0 ≤ qtil l - qchk l ∧
        qtil l - qchk l ≤
          ((M.Rblock i)⁻¹ *ᵥ (fun k : {l // M.firm l = i} => αtil k.1 - αchk k.1)) ⟨l, hl⟩) := by
  intro pchk αhat αtil αchk l hl
  obtain ⟨ha, hPD, hZ, hIS⟩ := hM
  set N := {l // M.firm l = i}
  set B : Matrix N N ℝ := M.Rblock i with hB
  set S := Finset.univ.filter (fun m => M.firm m = i) with hS
  have hsumN : ∀ g : ι → ℝ, ∑ m ∈ S, g m = ∑ k : N, g k.1 := by
    intro g
    exact Finset.sum_subtype S (fun x => by simp [hS]) g
  have hext : ∀ g : ι → ℝ, (∀ m, M.firm m ≠ i → g m = 0) → ∑ m, g m = ∑ k : N, g k.1 := by
    intro g hg
    rw [← hsumN, hS, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    split_ifs with h
    · rfl
    · exact hg m h
  -- properties of B
  have hBS : Bᵀ = B := by
    ext k k'
    simp only [hB, Market.Rblock, transpose_apply, submatrix_apply]
    exact hIS k'.1 k.1 (k'.2.trans k.2.symm)
  have hBZ : IsZMatrix B := by
    intro k k' hkk'
    exact hZ k.1 k'.1 (fun e => hkk' (Subtype.ext e))
  have hBPD : ∀ x : N → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (B *ᵥ x) := by
    intro x hx
    set X : ι → ℝ := fun m => if h : M.firm m = i then x ⟨m, h⟩ else 0 with hX
    have hXk : ∀ k : N, X k.1 = x k := by
      intro k; simp [hX, k.2]
    have hXoff : ∀ m, M.firm m ≠ i → X m = 0 := by
      intro m hm; simp [hX, hm]
    have hX0 : X ≠ 0 := by
      intro h; apply hx; funext k
      have := congrFun h k.1
      rw [hXk] at this; simpa using this
    have key := hPD X hX0
    have e : X ⬝ᵥ (M.R *ᵥ X) = x ⬝ᵥ (B *ᵥ x) := by
      simp only [dotProduct, mulVec]
      rw [hext (fun m => X m * ∑ j, M.R m j * X j) (fun m hm => by simp [hXoff m hm])]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hXk, hext (fun j => M.R k.1 j * X j) (fun j hj => by simp [hXoff j hj])]
      congr 1
      refine Finset.sum_congr rfl (fun k' _ => ?_)
      rw [hXk]; rfl
    rw [← e]; exact key
  -- translation of the firm's problem to the block
  set res : (ι → ℝ) → N → ℝ := fun x k => x k.1 with hres
  set αof : (ι → ℝ) → N → ℝ := fun p k => M.blockAlpha i p k.1 with hαof
  have hown : ∀ p x : ι → ℝ, ∀ k : N, M.ownDemand i x p k.1 = αof p k - (B *ᵥ res x) k := by
    intro p x k
    simp only [Market.ownDemand, Market.blockAlpha, hαof, hres, Pi.sub_apply, mulVec,
      dotProduct, hB, Market.Rblock, submatrix_apply]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => M.firm m = i)]
    rw [← hS, hsumN (fun m => M.R k.1 m * M.mix i x p m)]
    have e1 : ∑ k' : N, M.R k.1 k'.1 * M.mix i x p k'.1 = ∑ k' : N, M.R k.1 k'.1 * x k'.1 := by
      refine Finset.sum_congr rfl (fun k' _ => ?_)
      simp [Market.mix, k'.2]
    have e2 : ∑ m ∈ Finset.univ.filter (fun m => ¬ M.firm m = i), M.R k.1 m * M.mix i x p m =
        ∑ m ∈ Finset.univ.filter (fun m => M.firm m ≠ i), M.R k.1 m * p m := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hm' : M.firm m ≠ i := (Finset.mem_filter.1 hm).2
      simp [Market.mix, hm']
    rw [e1, e2]; ring
  have hprofit : ∀ p x : ι → ℝ, M.robustProfit w i p x =
      PRSBlock.obj B (res w) (αof p) (res x) := by
    intro p x
    simp only [Market.robustProfit, PRSBlock.obj, dotProduct]
    rw [← hS, hsumN (fun l => (x l - w l) * M.ownDemand i x p l)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hown]; rfl
  have hfeas : ∀ p x : ι → ℝ, M.RobustFeasible i p x ↔ (0 ≤ res x ∧ B *ᵥ res x ≤ αof p) := by
    intro p x
    constructor
    · intro h
      refine ⟨fun k => (h k.1 k.2).1, fun k => ?_⟩
      have := (h k.1 k.2).2
      rw [hown] at this
      simp only [Pi.sub_apply] at this ⊢; linarith
    · intro ⟨h1, h2⟩ m hm
      refine ⟨h1 ⟨m, hm⟩, ?_⟩
      have := hown p x ⟨m, hm⟩
      simp only at this
      rw [this]; have := h2 ⟨m, hm⟩; simp only [Pi.sub_apply] at *; linarith
  have hopt : ∀ p q : ι → ℝ, M.IsRobustBR w p q →
      (0 ≤ res q ∧ B *ᵥ res q ≤ αof p) ∧
      ∀ X : N → ℝ, 0 ≤ X → B *ᵥ X ≤ αof p →
        PRSBlock.obj B (res w) (αof p) X ≤ PRSBlock.obj B (res w) (αof p) (res q) := by
    intro p q hpq
    refine ⟨(hfeas p q).1 (hpq i).1, fun X hX0 hXB => ?_⟩
    set x : ι → ℝ := fun m => if h : M.firm m = i then X ⟨m, h⟩ else 0 with hx
    have hrx : res x = X := by
      funext k; simp [hres, hx, k.2]
    have hxf : M.RobustFeasible i p x := (hfeas p x).2 (by rw [hrx]; exact ⟨hX0, hXB⟩)
    have := (hpq i).2 x hxf
    rw [hprofit, hprofit, hrx] at this
    exact this
  -- intercepts
  have hαnn : ∀ p : ι → ℝ, 0 ≤ p → 0 ≤ αof p := by
    intro p hp k
    simp only [hαof, Market.blockAlpha, Pi.zero_apply]
    have : ∑ m ∈ Finset.univ.filter (fun m => M.firm m ≠ i), M.R k.1 m * p m ≤ 0 := by
      apply Finset.sum_nonpos
      intro m hm
      have hm' : M.firm m ≠ i := (Finset.mem_filter.1 hm).2
      exact mul_nonpos_of_nonpos_of_nonneg (hZ k.1 m (fun e => hm' (e ▸ k.2))) (hp m)
    have := ha k.1
    simp only [Pi.zero_apply] at this
    linarith
  have hαmono : ∀ p p' : ι → ℝ, p ≤ p' → αof p ≤ αof p' := by
    intro p p' hpp k
    simp only [hαof, Market.blockAlpha]
    have : ∑ m ∈ Finset.univ.filter (fun m => M.firm m ≠ i), M.R k.1 m * p' m ≤
        ∑ m ∈ Finset.univ.filter (fun m => M.firm m ≠ i), M.R k.1 m * p m := by
      apply Finset.sum_le_sum
      intro m hm
      have hm' : M.firm m ≠ i := (Finset.mem_filter.1 hm).2
      exact mul_le_mul_of_nonpos_left (hpp m) (hZ k.1 m (fun e => hm' (e ▸ k.2)))
    linarith
  have hpchk0 : 0 ≤ pchk := fun m => le_min (hphat m) (hptil m)
  have hwN : 0 ≤ res w := fun k => (hw k.1).le
  obtain ⟨hfc, hoc⟩ := hopt _ _ hqchk
  obtain ⟨hfh, hoh⟩ := hopt _ _ hqhat
  obtain ⟨hft, hot⟩ := hopt _ _ hqtil
  have R1 := PRSBlock.block_lemma2 B hBS hBZ hBPD (res w) hwN (αof pchk) (αof phat)
    (hαnn _ hpchk0) (hαmono _ _ (fun m => min_le_left _ _)) (res qchk) (res qhat) hfc hfh hoc hoh
    ⟨l, hl⟩
  have R2 := PRSBlock.block_lemma2 B hBS hBZ hBPD (res w) hwN (αof pchk) (αof ptil)
    (hαnn _ hpchk0) (hαmono _ _ (fun m => min_le_right _ _)) (res qchk) (res qtil) hfc hft hoc hot
    ⟨l, hl⟩
  exact ⟨R1, R2⟩
