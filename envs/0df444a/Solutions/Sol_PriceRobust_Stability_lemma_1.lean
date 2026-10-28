-- Prove2me | solution 1 for PriceRobust.Stability.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T20:38:44.79957+00:00
-- url     : https://prove2.me/submissions/7a6b5671-f7c8-4bde-8a79-7904a7dc7e2b

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

namespace PRB1
open PriceRobust.Stability Matrix in
theorem lam_lemma {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (M : Market ι F) (hM : M.Standing) :
    (∀ l m, 0 ≤ M.Lam l m) ∧ spectralRadius ℂ (M.Lam.map (algebraMap ℝ ℂ)) < 1 := by
  obtain ⟨_, hPD, hZ, hIS⟩ := hM
  have hRZ : IsZMatrix M.R := hZ
  have hRZP : IsZPMatrix M.R := PRB1.ZP_of_pd M.R hRZ hPD
  have hT : ∀ l m, M.Tmat l m = if M.firm l = M.firm m then M.R l m else 0 := by
    intro l m
    simp only [Market.Tmat]
    split_ifs with h
    · exact (hIS l m h).symm
    · rfl
  have hTZ : IsZMatrix M.Tmat := by
    intro l m hlm
    rw [hT]; split_ifs
    · exact hZ l m hlm
    · exact le_rfl
  have hRT : ∀ l m, M.R l m ≤ M.Tmat l m := by
    intro l m
    rw [hT]; split_ifs with h
    · exact le_rfl
    · exact hZ l m (fun e => h (e ▸ rfl))
  -- positive vector for R
  obtain ⟨hRu, hRinv⟩ := PRB1.inv_nonneg M.R M.R hRZP hRZ (fun _ _ => le_rfl)
  set y : ι → ℝ := M.R⁻¹ *ᵥ (fun _ => 1) with hy
  have hRy : M.R *ᵥ y = fun _ => 1 := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hRu, Matrix.one_mulVec]
  have hypos : ∀ i, 0 < y i := by
    intro i
    simp only [hy, mulVec, dotProduct, mul_one]
    apply Finset.sum_pos' (fun j _ => hRinv i j)
    by_contra hall
    push Not at hall
    have hz : ∀ j, M.R⁻¹ i j = 0 := fun j => le_antisymm (hall j (Finset.mem_univ j)) (hRinv i j)
    have : (M.R⁻¹ * M.R) i i = 0 := by simp [Matrix.mul_apply, hz]
    rw [Matrix.nonsing_inv_mul _ hRu, Matrix.one_apply_eq] at this
    exact one_ne_zero this
  have hTy : ∀ i, 0 < (M.Tmat *ᵥ y) i := by
    intro i
    have : (M.R *ᵥ y) i ≤ (M.Tmat *ᵥ y) i := by
      simp only [mulVec, dotProduct]
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hRT i j) (hypos j).le)
    rw [hRy] at this
    linarith
  have hTZP : IsZPMatrix M.Tmat := PRB1.ZP_of_pos M.Tmat hTZ y hypos hTy
  obtain ⟨hTu, hTinv⟩ := PRB1.inv_nonneg M.Tmat M.Tmat hTZP hTZ (fun _ _ => le_rfl)
  have hc := (PRB1.b1c M.R M.Tmat hRZP hTZ hRT).2
  have hLam : M.Lam = M.Tmat⁻¹ * (M.Tmat - M.R) := by
    simp only [Market.Lam]
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ hTu]
  have hnn : ∀ l m, 0 ≤ M.Lam l m := by
    intro l m
    rw [hLam, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hTinv l j) (by simp [hRT j m]))
  refine ⟨hnn, PRB1.b1g M.Lam hnn ?_⟩
  have : (1 : Matrix ι ι ℝ) - M.Lam = M.Tmat⁻¹ * M.R := by
    simp only [Market.Lam]; abel
  rw [this]; exact hc

open PriceRobust.Stability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ZP_sub (Z : Matrix ι ι ℝ) (hZ : IsZPMatrix Z) (p : ι → Prop) [DecidablePred p] :
    IsZPMatrix (Z.submatrix (fun x : {l // p l} => x.1) (fun x : {l // p l} => x.1)) := by
  refine ⟨fun i j hij => hZ.1 i j (fun h => hij (Subtype.ext h)), fun T hT => ?_⟩
  have h := hZ.2 (T.map (Function.Embedding.subtype p)) (hT.map)
  let e : T ≃ (T.map (Function.Embedding.subtype p) : Finset ι) :=
    { toFun := fun t => ⟨t.1.1, Finset.mem_map_of_mem _ t.2⟩
      invFun := fun u => ⟨⟨u.1, by
          obtain ⟨t, _, he⟩ := Finset.mem_map.1 u.2; rw [← he]; exact t.2⟩, by
          obtain ⟨t, ht, he⟩ := Finset.mem_map.1 u.2
          have : t = ⟨u.1, by rw [← he]; exact t.2⟩ := Subtype.ext he
          rw [← this]; exact ht⟩
      left_inv := fun t => rfl
      right_inv := fun u => rfl }
  rw [← det_submatrix_equiv_self e] at h
  exact h

end PRB1

namespace PRL1
open PriceRobust.Stability

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F] (M : Market ι F)

def K (i : F) (p : ι → ℝ) : Set (ι → ℝ) :=
  {x | (∀ l, M.firm l ≠ i → x l = p l) ∧ M.RobustFeasible i p x}

lemma mix_self {i : F} {p x : ι → ℝ} (hx : ∀ l, M.firm l ≠ i → x l = p l) : M.mix i x p = x := by
  funext m; simp only [Market.mix]; split_ifs with h
  · rfl
  · exact (hx m h).symm

lemma mix_mix (i : F) (x p : ι → ℝ) : M.mix i (M.mix i x p) p = M.mix i x p := by
  funext m; simp only [Market.mix]; split_ifs <;> rfl

lemma own_mix (i : F) (x p : ι → ℝ) : M.ownDemand i (M.mix i x p) p = M.ownDemand i x p := by
  simp only [Market.ownDemand, mix_mix]

lemma feas_mix (i : F) (x p : ι → ℝ) :
    M.RobustFeasible i p (M.mix i x p) ↔ M.RobustFeasible i p x := by
  simp only [Market.RobustFeasible, own_mix]
  constructor
  · intro h l hl; have := h l hl; simpa [Market.mix, hl] using this
  · intro h l hl; have := h l hl; simpa [Market.mix, hl] using this

lemma profit_mix (w : ι → ℝ) (i : F) (x p : ι → ℝ) :
    M.robustProfit w i p (M.mix i x p) = M.robustProfit w i p x := by
  simp only [Market.robustProfit, own_mix]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Finset.mem_filter] at hl
  simp [Market.mix, hl.2]

lemma mix_mem_K {i : F} {x p : ι → ℝ} (hx : M.RobustFeasible i p x) : M.mix i x p ∈ K M i p :=
  ⟨fun l hl => by simp [Market.mix, hl], (feas_mix M i x p).2 hx⟩

lemma own_cont (i : F) (p : ι → ℝ) (l : ι) : Continuous (fun x => M.ownDemand i x p l) := by
  simp only [Market.ownDemand, Pi.sub_apply, Matrix.mulVec, dotProduct, Market.mix]
  refine continuous_const.sub (continuous_finset_sum _ (fun m _ => continuous_const.mul ?_))
  by_cases h : M.firm m = i
  · simp only [h, if_true]; exact continuous_apply m
  · simp only [h, if_false]; exact continuous_const

lemma profit_cont (w : ι → ℝ) (i : F) (p : ι → ℝ) : Continuous (fun x => M.robustProfit w i p x) := by
  simp only [Market.robustProfit]
  exact continuous_finset_sum _ (fun l _ =>
    ((continuous_apply l).sub continuous_const).mul (own_cont M i p l))

lemma K_closed (i : F) (p : ι → ℝ) : IsClosed (K M i p) := by
  have : K M i p = ⋂ l, {x : ι → ℝ | (M.firm l ≠ i → x l = p l) ∧
      (M.firm l = i → 0 ≤ x l ∧ 0 ≤ M.ownDemand i x p l)} := by
    ext x; simp only [K, Market.RobustFeasible, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro ⟨h1, h2⟩ l; exact ⟨h1 l, h2 l⟩
    · intro h; exact ⟨fun l => (h l).1, fun l => (h l).2⟩
  rw [this]
  refine isClosed_iInter (fun l => ?_)
  by_cases h : M.firm l = i
  · simp only [h, ne_eq, not_true_eq_false, IsEmpty.forall_iff, true_and, forall_const]
    exact (isClosed_le continuous_const (continuous_apply l)).inter
      (isClosed_le continuous_const (own_cont M i p l))
  · simp only [h, ne_eq, not_false_eq_true, forall_const, IsEmpty.forall_iff, and_true]
    exact isClosed_eq (continuous_apply l) continuous_const

lemma sum_filter_eq_sub {i : F} (f : ι → ℝ) :
    ∑ m ∈ Finset.univ.filter (fun m => M.firm m ≠ i), f m = ∑ m : {m // ¬ M.firm m = i}, f m :=
  Finset.sum_subtype _ (fun m => by simp) f

/-- block decomposition of the demand. -/
lemma own_block {i : F} {p x : ι → ℝ} (l : {l // M.firm l = i}) :
    M.ownDemand i x p l.1 = M.blockAlpha i p l.1 - (M.Rblock i *ᵥ (fun k => x k.1)) l := by
  simp only [Market.ownDemand, Market.blockAlpha, Pi.sub_apply, Market.Rblock, Matrix.mulVec,
    dotProduct, Matrix.submatrix_apply]
  rw [sum_filter_eq_sub M (fun m => M.R l.1 m * p m),
    ← Fintype.sum_subtype_add_sum_subtype (fun m => M.firm m = i)
      (fun m => M.R l.1 m * M.mix i x p m)]
  have h1 : ∑ m : {m // M.firm m = i}, M.R l.1 m * M.mix i x p m = ∑ m : {m // M.firm m = i}, M.R l.1 m * x m :=
    Finset.sum_congr rfl (fun m _ => by simp [Market.mix, m.2])
  have h2 : ∑ m : {m // ¬ M.firm m = i}, M.R l.1 m * M.mix i x p m = ∑ m : {m // ¬ M.firm m = i}, M.R l.1 m * p m :=
    Finset.sum_congr rfl (fun m _ => by simp [Market.mix, m.2])
  rw [h1, h2]; ring

end PRL1

namespace PRL1
open PriceRobust.Stability

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F] (M : Market ι F)

lemma K_bdd (hM : M.Standing) (i : F) (p : ι → ℝ) :
    ∃ hi : ι → ℝ, ∀ x ∈ K M i p, ∀ l, M.firm l = i → x l ≤ hi l := by
  have hRZP : IsZPMatrix M.R := PRB1.ZP_of_pd M.R hM.2.2.1 hM.2.1
  have hb : IsZPMatrix (M.Rblock i) := PRB1.ZP_sub M.R hRZP (fun l => M.firm l = i)
  obtain ⟨hu, _⟩ := PRB1.inv_nonneg _ _ hb hb.1 (fun _ _ => le_rfl)
  set y := (M.Rblock i)⁻¹ *ᵥ (fun k : {l // M.firm l = i} => M.blockAlpha i p k.1) with hy
  refine ⟨fun l => if h : M.firm l = i then y ⟨l, h⟩ else 0, ?_⟩
  intro x hx l hl
  simp only [hl, dite_true]
  have e : (M.Rblock i *ᵥ y) = fun k => M.blockAlpha i p k.1 := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hmono := PRB1.mono _ rfl (M.Rblock i) hb (y - fun k => x k.1) (by
    intro k
    rw [Matrix.mulVec_sub, Pi.sub_apply, e]
    have := (hx.2 k.1 k.2).2
    rw [own_block M (p := p) (x := x) k] at this
    linarith) ⟨l, hl⟩
  simp only [Pi.sub_apply] at hmono
  linarith

lemma K_compact (hM : M.Standing) (i : F) (p : ι → ℝ) : IsCompact (K M i p) := by
  obtain ⟨hi, hhi⟩ := K_bdd M hM i p
  let lo : ι → ℝ := fun l => if M.firm l = i then 0 else p l
  let up : ι → ℝ := fun l => if M.firm l = i then hi l else p l
  refine (isCompact_Icc (a := lo) (b := up)).of_isClosed_subset (K_closed M i p) ?_
  intro x hx
  refine ⟨fun l => ?_, fun l => ?_⟩
  · simp only [lo]; split_ifs with h
    · exact (hx.2 l h).1
    · exact le_of_eq (hx.1 l h).symm
  · simp only [up]; split_ifs with h
    · exact hhi x hx l h
    · exact le_of_eq (hx.1 l h)

lemma K_ne (hM : M.Standing) (i : F) (p : ι → ℝ) (hp : 0 ≤ p) : M.mix i 0 p ∈ K M i p := by
  refine ⟨fun l hl => by simp [Market.mix, hl], fun l hl => ⟨by simp [Market.mix, hl], ?_⟩⟩
  rw [own_mix]
  simp only [Market.ownDemand, Pi.sub_apply, Matrix.mulVec, dotProduct]
  have ha : 0 ≤ M.a l := hM.1 l
  have : ∑ m, M.R l m * M.mix i 0 p m ≤ 0 := by
    apply Finset.sum_nonpos; intro m _
    simp only [Market.mix]
    split_ifs with h
    · simp
    · exact mul_nonpos_of_nonpos_of_nonneg (hM.2.2.1 l m (fun e => h (e ▸ hl))) (hp m)
  linarith

lemma mid_off {i : F} {p x y : ι → ℝ} (hx : x ∈ K M i p) (hy : y ∈ K M i p) :
    ∀ l, M.firm l ≠ i → ((1/2:ℝ) • (x + y)) l = p l := by
  intro l hl; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hx.1 l hl, hy.1 l hl]; ring

lemma mid_profit (w : ι → ℝ) {i : F} {p x y : ι → ℝ} (hx : x ∈ K M i p) (hy : y ∈ K M i p) :
    M.robustProfit w i p ((1/2:ℝ) • (x + y)) -
        (M.robustProfit w i p x + M.robustProfit w i p y) / 2
      = (1/4) * ((x - y) ⬝ᵥ (M.R *ᵥ (x - y))) := by
  have hmx := mix_self M hx.1
  have hmy := mix_self M hy.1
  have hmm := mix_self M (mid_off M hx hy)
  simp only [Market.robustProfit, Market.ownDemand, hmx, hmy, hmm]
  have hd : (x - y) ⬝ᵥ (M.R *ᵥ (x - y)) =
      ∑ l ∈ Finset.univ.filter (fun l => M.firm l = i), (x l - y l) * (M.R *ᵥ (x - y)) l := by
    simp only [dotProduct]
    rw [Finset.sum_filter_of_ne]
    · rfl
    intro l _ hne
    by_contra h
    apply hne
    simp [hx.1 l h, hy.1 l h]
  rw [hd, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_add, Pi.sub_apply, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul]
  ring

lemma uniq (hM : M.Standing) (w : ι → ℝ) {i : F} {p x y : ι → ℝ} (hx : x ∈ K M i p)
    (hy : y ∈ K M i p)
    (hmx : ∀ z ∈ K M i p, M.robustProfit w i p z ≤ M.robustProfit w i p x)
    (hmy : ∀ z ∈ K M i p, M.robustProfit w i p z ≤ M.robustProfit w i p y) : x = y := by
  by_contra hne
  have hoff := mid_off M hx hy
  have hm : (1/2:ℝ) • (x + y) ∈ K M i p := by
    refine ⟨hoff, fun l hl => ⟨?_, ?_⟩⟩
    · simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      linarith [(hx.2 l hl).1, (hy.2 l hl).1]
    · have e : M.ownDemand i ((1/2:ℝ) • (x + y)) p l =
          (M.ownDemand i x p l + M.ownDemand i y p l) / 2 := by
        simp only [Market.ownDemand, mix_self M hx.1, mix_self M hy.1, mix_self M hoff,
          Matrix.mulVec_smul, Matrix.mulVec_add, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
          smul_eq_mul]
        ring
      rw [e]; linarith [(hx.2 l hl).2, (hy.2 l hl).2]
  have hpos : 0 < (x - y) ⬝ᵥ (M.R *ᵥ (x - y)) := hM.2.1 _ (sub_ne_zero.2 hne)
  have := mid_profit M w hx hy
  have h1 := hmx _ hm
  have h2 := hmy _ hm
  linarith

end PRL1

open PriceRobust.Stability in
theorem solution {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (M : Market ι F) (hM : M.Standing) (w : ι → ℝ) (hw : ∀ l, 0 < w l)
    (p : ι → ℝ) (hp : 0 ≤ p) :
    ∃! q : ι → ℝ, M.IsRobustBR w p q := by
  have hex : ∀ i : F, ∃ x ∈ PRL1.K M i p, ∀ z ∈ PRL1.K M i p,
      M.robustProfit w i p z ≤ M.robustProfit w i p x := by
    intro i
    obtain ⟨x, hx, hmax⟩ := (PRL1.K_compact M hM i p).exists_isMaxOn ⟨_, PRL1.K_ne M hM i p hp⟩
      (PRL1.profit_cont M w i p).continuousOn
    exact ⟨x, hx, fun z hz => hmax hz⟩
  choose qi hqi hqmax using hex
  set q : ι → ℝ := fun l => qi (M.firm l) l with hq
  have hmixq : ∀ i, M.mix i q p = qi i := by
    intro i; funext m; simp only [Market.mix, hq]; split_ifs with h
    · rw [h]
    · exact ((hqi i).1 m h).symm
  have hBR : ∀ q' : ι → ℝ, (∀ i, M.mix i q' p ∈ PRL1.K M i p ∧ ∀ z ∈ PRL1.K M i p,
      M.robustProfit w i p z ≤ M.robustProfit w i p (M.mix i q' p)) → M.IsRobustBR w p q' := by
    intro q' h i
    refine ⟨(PRL1.feas_mix M i q' p).1 (h i).1.2, fun x hx => ?_⟩
    rw [← PRL1.profit_mix M w i q' p, ← PRL1.profit_mix M w i x p]
    exact (h i).2 _ (PRL1.mix_mem_K M hx)
  refine ⟨q, hBR q (fun i => by rw [hmixq]; exact ⟨hqi i, hqmax i⟩), ?_⟩
  intro q' hq'
  funext l
  have h1 : M.mix (M.firm l) q' p ∈ PRL1.K M (M.firm l) p := PRL1.mix_mem_K M (hq' (M.firm l)).1
  have hmax' : ∀ z ∈ PRL1.K M (M.firm l) p,
      M.robustProfit w (M.firm l) p z ≤ M.robustProfit w (M.firm l) p (M.mix (M.firm l) q' p) := by
    intro z hz; rw [PRL1.profit_mix]; exact (hq' (M.firm l)).2 z hz.2
  have := PRL1.uniq M hM w h1 (hqi (M.firm l)) hmax' (hqmax (M.firm l))
  have e1 : M.mix (M.firm l) q' p l = q' l := by simp [Market.mix]
  rw [← e1, this]
