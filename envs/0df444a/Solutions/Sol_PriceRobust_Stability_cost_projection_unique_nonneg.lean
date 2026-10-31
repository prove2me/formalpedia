-- Prove2me | solution 1 for PriceRobust.Stability.cost_projection_unique_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:59:33.770904+00:00
-- url     : https://prove2.me/submissions/50fb944a-6fde-412d-9652-11465739a2b2

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

open PriceRobust.Stability Matrix in
theorem solution {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (M : Market ι F) (hM : M.Standing) (w : ι → ℝ) (hw : ∀ l, 0 < w l) :
    (∃! w' : ι → ℝ, M.IsCostProjection w w') ∧
      ∀ w' : ι → ℝ, M.IsCostProjection w w' → 0 ≤ w' := by
  obtain ⟨ha, hPD, hZ, hIS⟩ := hM
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
  have hSZ : IsZMatrix (M.R + M.Tmat) := by
    intro l m h
    simp only [Matrix.add_apply]
    linarith [hRZ l m h, hTZ l m h]
  have hSy : ∀ i, 0 < ((M.R + M.Tmat) *ᵥ y) i := by
    intro i
    rw [Matrix.add_mulVec, hRy]
    simp only [Pi.add_apply]
    linarith [hTy i]
  have hSZP : IsZPMatrix (M.R + M.Tmat) := PRB1.ZP_of_pos _ hSZ y hypos hSy
  obtain ⟨hSu, -⟩ := PRB1.inv_nonneg _ _ hSZP hSZ (fun _ _ => le_rfl)
  -- the quadratic form of T(R) is nonnegative (sum over firms of the forms of R)
  have hTform : ∀ s : ι → ℝ, 0 ≤ s ⬝ᵥ (M.Tmat *ᵥ s) := by
    intro s
    have hmaps : ∀ l ∈ (Finset.univ : Finset ι), M.firm l ∈ Finset.univ.image M.firm :=
      fun l _ => Finset.mem_image_of_mem _ (Finset.mem_univ l)
    simp only [dotProduct]
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_nonneg
    intro i _
    set si : ι → ℝ := fun m => if M.firm m = i then s m else 0 with hsi
    have e : ∑ l ∈ Finset.univ.filter (fun l => M.firm l = i), s l * (M.Tmat *ᵥ s) l =
        si ⬝ᵥ (M.R *ᵥ si) := by
      rw [Finset.sum_filter]
      simp only [dotProduct]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      by_cases hl : M.firm l = i
      · rw [if_pos hl]
        simp only [hsi, if_pos hl]
        congr 1
        simp only [mulVec, dotProduct]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [hT]
        by_cases hm : M.firm m = i
        · rw [if_pos (hl.trans hm.symm), if_pos hm]
        · rw [if_neg (fun h => hm (h.symm.trans hl)), if_neg hm]; simp
      · rw [if_neg hl]; simp [hsi, hl]
    rw [e]
    by_cases h0 : si = 0
    · rw [h0]; simp
    · exact (hPD si h0).le
  -- the LCP matrix Ψ(R) R is positive definite
  set A : Matrix ι ι ℝ := M.Psi * M.R with hA
  have hApd : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x) := by
    intro x hx
    set s := (M.R + M.Tmat)⁻¹ *ᵥ (M.R *ᵥ x) with hs
    have hSs : (M.R + M.Tmat) *ᵥ s = M.R *ᵥ x := by
      rw [hs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hSu, Matrix.one_mulVec]
    have hTs : M.Tmat *ᵥ s = M.R *ᵥ (x - s) := by
      rw [Matrix.add_mulVec] at hSs
      rw [Matrix.mulVec_sub, ← hSs]; abel
    have hAx : A *ᵥ x = M.Tmat *ᵥ s := by
      rw [hA, Market.Psi, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have esplit : x ⬝ᵥ (A *ᵥ x) = s ⬝ᵥ (M.Tmat *ᵥ s) + (x - s) ⬝ᵥ (M.R *ᵥ (x - s)) := by
      rw [hAx, ← hTs, ← add_dotProduct]; congr 1; abel
    rw [esplit]
    by_cases hxs : x - s = 0
    · exfalso
      rw [hxs, Matrix.mulVec_zero] at hTs
      have hs0 : s = 0 := by
        have := congrArg (fun v => M.Tmat⁻¹ *ᵥ v) hTs
        simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hTu] using this
      apply hx
      rw [hs0, sub_zero] at hxs; exact hxs
    · linarith [hTform s, hPD _ hxs]
  -- Q(w') = c + A (w - w')
  set c : ι → ℝ := M.Qw w with hc
  have hQ : ∀ w' : ι → ℝ, M.Qw w' = c + A *ᵥ (w - w') := by
    intro w'
    simp only [hc, Market.Qw, hA, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    abel
  -- nonnegativity of every solution
  have hnn : ∀ w' : ι → ℝ, M.IsCostProjection w w' → 0 ≤ w' := by
    intro w' ⟨hle, hcomp, hQnn⟩
    set d0 := (M.R + M.Tmat)⁻¹ *ᵥ (M.a - M.R *ᵥ w') with hd0
    have hSd0 : (M.R + M.Tmat) *ᵥ d0 = M.a - M.R *ᵥ w' := by
      rw [hd0, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hSu, Matrix.one_mulVec]
    have hQd : M.Qw w' = M.Tmat *ᵥ d0 := by
      simp only [Market.Qw, Market.Psi, hd0]
      rw [← Matrix.mulVec_sub, ← Matrix.mulVec_mulVec]
    have hd0nn : ∀ l, 0 ≤ d0 l := by
      have e : d0 = M.Tmat⁻¹ *ᵥ M.Qw w' := by
        rw [hQd, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hTu, Matrix.one_mulVec]
      intro l
      rw [e]
      simp only [mulVec, dotProduct]
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (hTinv l j) (hQnn j))
    have hterm : ∀ l, M.Qw w' l * (w l - w' l) = 0 := by
      have hnn' : ∀ l ∈ Finset.univ, 0 ≤ M.Qw w' l * (w l - w' l) :=
        fun l _ => mul_nonneg (hQnn l) (by linarith [hle l])
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn').1 (by simpa [dotProduct] using hcomp)
      exact fun l => this l (Finset.mem_univ l)
    -- on {w' < 0}, (R w')_l ≥ 0
    have hRw : ∀ l, w' l < 0 → 0 ≤ (M.R *ᵥ w') l := by
      intro l hl
      have hQl : (M.Tmat *ᵥ d0) l = 0 := by
        have h := hterm l
        rw [hQd] at h
        rcases mul_eq_zero.1 h with h' | h'
        · exact h'
        · have := hw l; linarith
      have hRd : (M.R *ᵥ d0) l ≤ (M.Tmat *ᵥ d0) l := by
        simp only [mulVec, dotProduct]
        exact Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_right (hRT l m) (hd0nn m))
      have h2 := congrFun hSd0 l
      simp only [Matrix.add_mulVec, Pi.add_apply, Pi.sub_apply] at h2
      have := ha l
      simp only [Pi.zero_apply] at this
      linarith
    set n : ι → ℝ := fun l => max (-w' l) 0 with hn
    set pp : ι → ℝ := fun l => max (w' l) 0 with hpp
    have hwpn : w' = pp - n := by
      funext l
      simp only [hn, hpp, Pi.sub_apply]
      rcases le_total (w' l) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    have hRn : ∀ l, 0 < n l → (M.R *ᵥ n) l ≤ 0 := by
      intro l hl
      have hwl : w' l < 0 := by
        by_contra h; push Not at h
        have : n l = 0 := by simp only [hn]; exact max_eq_right (by linarith)
        linarith
      have h1 := hRw l hwl
      have hppl : pp l = 0 := by simp only [hpp]; exact max_eq_right hwl.le
      have h2 : (M.R *ᵥ pp) l ≤ 0 := by
        simp only [mulVec, dotProduct]
        apply Finset.sum_nonpos
        intro m _
        by_cases hm : l = m
        · subst hm; rw [hppl, mul_zero]
        · exact mul_nonpos_of_nonpos_of_nonneg (hZ l m hm) (le_max_right _ _)
      rw [hwpn, Matrix.mulVec_sub] at h1
      simp only [Pi.sub_apply] at h1
      linarith
    have hform : n ⬝ᵥ (M.R *ᵥ n) ≤ 0 := by
      apply Finset.sum_nonpos
      intro l _
      rcases (le_max_right (-w' l) 0).lt_or_eq with h | h
      · exact mul_nonpos_of_nonneg_of_nonpos h.le (hRn l h)
      · have : n l = 0 := h.symm
        rw [this, zero_mul]
    have hn0 : n = 0 := by
      by_contra h
      linarith [hPD n h]
    intro l
    have := congrFun hn0 l
    simp only [hn, Pi.zero_apply] at this
    have := le_max_left (-w' l) 0
    simp only [Pi.zero_apply]
    linarith
  refine ⟨?_, hnn⟩
  -- existence, from the LCP with a positive definite matrix
  obtain ⟨z, hz0, hQz, hcz⟩ := PRSLCP.lcp_exists A hApd c
  refine ⟨w - z, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro l; have := hz0 l; simp only [Pi.sub_apply, Pi.zero_apply] at this ⊢; linarith
  · rw [hQ, sub_sub_cancel, dotProduct_comm]; exact hcz
  · rw [hQ, sub_sub_cancel]; exact hQz
  -- uniqueness
  intro v ⟨hle, hcomp, hQnn⟩
  set z' := w - v with hz'
  have hQv : M.Qw v = c + A *ᵥ z' := hQ v
  have hz'0 : 0 ≤ z' := fun l => by simp only [hz', Pi.sub_apply, Pi.zero_apply]; linarith [hle l]
  have hcz' : z' ⬝ᵥ (c + A *ᵥ z') = 0 := by rw [← hQv, dotProduct_comm]; exact hcomp
  have hQv0 : 0 ≤ c + A *ᵥ z' := hQv ▸ hQnn
  have hdd : (z' - z) ⬝ᵥ (A *ᵥ (z' - z)) ≤ 0 := by
    have e : (z' - z) ⬝ᵥ (A *ᵥ (z' - z)) =
        z' ⬝ᵥ (c + A *ᵥ z') + z ⬝ᵥ (c + A *ᵥ z) - z' ⬝ᵥ (c + A *ᵥ z) - z ⬝ᵥ (c + A *ᵥ z') := by
      simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_add]
      ring
    have h1 : 0 ≤ z' ⬝ᵥ (c + A *ᵥ z) :=
      Finset.sum_nonneg (fun l _ => mul_nonneg (hz'0 l) (hQz l))
    have h2 : 0 ≤ z ⬝ᵥ (c + A *ᵥ z') :=
      Finset.sum_nonneg (fun l _ => mul_nonneg (hz0 l) (hQv0 l))
    rw [e, hcz, hcz']; linarith
  have : z' - z = 0 := by
    by_contra h
    linarith [hApd _ h]
  have : z' = z := sub_eq_zero.1 this
  rw [hz'] at this
  rw [← this]; abel
