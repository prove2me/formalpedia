-- Prove2me | solution 1 for PriceRobust.Stability.absolute_norm_near_spectral_radius
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T20:33:19.226987+00:00
-- url     : https://prove2.me/submissions/4ca2b509-098a-4fd7-a797-9392c60350b7

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

end PRB1

namespace PRAbs
open PriceRobust.Stability Filter Topology
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma spec_ne_top (Lc : Matrix ι ι ℂ) : spectralRadius ℂ Lc ≠ ⊤ := by
  have hfin : (spectrum ℂ Lc).Finite :=
    (Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic Lc).ne_zero).subset
      (fun r hr => Matrix.mem_spectrum_iff_isRoot_charpoly.1 hr)
  apply ne_of_lt
  unfold spectralRadius
  rw [← hfin.coe_toFinset]
  simp only [Finset.mem_coe]
  rw [← Finset.sup_eq_iSup, Finset.sup_lt_iff (by simp)]
  intro r _
  exact ENNReal.coe_lt_top

lemma pow_nonneg' (L : Matrix ι ι ℝ) (hL : ∀ l m, 0 ≤ L l m) (n : ℕ) : ∀ l m, 0 ≤ (L ^ n) l m := by
  induction n with
  | zero => intro l m; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    intro l m; rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (ih l j) (hL j m))

open scoped Matrix.Norms.Operator in
/-- Gelfand: entries of `L^n` are eventually bounded by `s'^n` for any `s' > ρ`. -/
lemma entry_bound (L : Matrix ι ι ℝ) (s' : ℝ) (hs' : spectralRadius ℂ (L.map (algebraMap ℝ ℂ)) < ENNReal.ofReal s') :
    ∀ᶠ n : ℕ in atTop, ∀ l m, |(L ^ n) l m| ≤ s' ^ n := by
  set Lc := L.map (algebraMap ℝ ℂ)
  have hG := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius Lc
  have hev := hG.eventually (gt_mem_nhds hs')
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1 l m
  have hs'pos : 0 < s' := by
    by_contra h; push Not at h
    rw [ENNReal.ofReal_of_nonpos h] at hs'; exact absurd hs' (not_lt_bot)
  -- ‖Lc^n‖ < s'^n
  have hlt : (‖Lc ^ n‖₊ : ℝ≥0∞) < ENNReal.ofReal s' ^ n := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have := ENNReal.pow_lt_pow_left (show n ≠ 0 by omega) hn
    rwa [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hn0,
      ENNReal.rpow_one] at this
  have hlt' : ‖Lc ^ n‖ < s' ^ n := by
    rw [← ENNReal.ofReal_pow hs'pos.le] at hlt
    rw [← enorm_eq_nnnorm, ← ofReal_norm] at hlt
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hlt
  have hentry : ‖(Lc ^ n) l m‖ ≤ ‖Lc ^ n‖ := by
    rw [Matrix.linfty_opNorm_def]
    have h1 : ‖(Lc ^ n) l m‖₊ ≤ ∑ j, ‖(Lc ^ n) l j‖₊ :=
      Finset.single_le_sum (f := fun j => ‖(Lc ^ n) l j‖₊) (fun _ _ => by positivity) (Finset.mem_univ m)
    have h2 : ∑ j, ‖(Lc ^ n) l j‖₊ ≤ (Finset.univ : Finset ι).sup fun i => ∑ j, ‖(Lc ^ n) i j‖₊ :=
      Finset.le_sup (f := fun i => ∑ j, ‖(Lc ^ n) i j‖₊) (Finset.mem_univ l)
    exact_mod_cast h1.trans h2
  have hmap : (Lc ^ n) l m = ((L ^ n) l m : ℂ) := by
    have : Lc ^ n = (L ^ n).map (algebraMap ℝ ℂ) := by
      simp only [Lc]
      rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_pow]
    rw [this]; rfl
  rw [hmap, Complex.norm_real, Real.norm_eq_abs] at hentry
  linarith

end PRAbs

open PriceRobust.Stability Filter Topology in
theorem solution {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (M : Market ι F) (hM : M.Standing) (ε : ℝ) (hε : 0 < ε) :
    ∃ ν : Seminorm ℝ (ι → ℝ), (∀ x, ν x = 0 → x = 0) ∧
      (∀ x, ν x = ν (fun l => |x l|)) ∧
      ∀ x, ENNReal.ofReal (ν (M.Lam *ᵥ x)) ≤
        (spectralRadius ℂ (M.Lam.map (algebraMap ℝ ℂ)) + ENNReal.ofReal ε) *
          ENNReal.ofReal (ν x) := by
  set L := M.Lam with hLdef
  have hL : ∀ l m, 0 ≤ L l m := (PRB1.lam_lemma M hM).1
  set ρ := spectralRadius ℂ (L.map (algebraMap ℝ ℂ)) with hρ
  have hρt : ρ ≠ ⊤ := PRAbs.spec_ne_top _
  set r := ρ.toReal
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hρr : ρ = ENNReal.ofReal r := (ENNReal.ofReal_toReal hρt).symm
  set s := r + ε
  set s' := r + ε / 2
  have hs : 0 < s := by positivity
  have hs'pos : 0 < s' := by positivity
  have hss' : s' < s := by simp only [s, s']; linarith
  have hlt : ρ < ENNReal.ofReal s' := by
    rw [hρr]; exact (ENNReal.ofReal_lt_ofReal_iff hs'pos).2 (by simp only [s']; linarith)
  obtain ⟨N, hN⟩ := (PRAbs.entry_bound L s' hlt).exists_forall_of_atTop
  -- terms
  set t : ℕ → ι → ℝ := fun n l => (∑ m, (L ^ n) l m) / s ^ n with ht
  have htnn : ∀ n l, 0 ≤ t n l := fun n l =>
    div_nonneg (Finset.sum_nonneg (fun m _ => PRAbs.pow_nonneg' L hL n l m)) (by positivity)
  have hsum : ∀ l, Summable (fun n => t n l) := by
    intro l
    have hq : Summable (fun n : ℕ => (Fintype.card ι : ℝ) * (s' / s) ^ n) :=
      (summable_geometric_of_lt_one (by positivity) ((div_lt_one hs).2 hss')).mul_left _
    refine hq.of_norm_bounded_eventually ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [Real.norm_of_nonneg (htnn n l), ht]
    simp only
    rw [div_pow, ← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
    calc ∑ m, (L ^ n) l m ≤ ∑ _m : ι, s' ^ n :=
          Finset.sum_le_sum (fun m _ => (le_abs_self _).trans (hN n hn l m))
      _ = _ := by simp
  set v : ι → ℝ := fun l => ∑' n, t n l with hv
  have hv1 : ∀ l, 1 ≤ v l := by
    intro l
    have := (hsum l).le_tsum 0 (fun n _ => htnn n l)
    have h0 : t 0 l = 1 := by simp [ht, Matrix.one_apply]
    rw [h0] at this; exact this
  have hvpos : ∀ l, 0 < v l := fun l => lt_of_lt_of_le one_pos (hv1 l)
  -- L v ≤ s v
  have hLv : ∀ l, (L *ᵥ v) l ≤ s * v l := by
    intro l
    have hshift : ∀ n, ∑ k, L l k * t n k = s * t (n + 1) l := by
      intro n
      have e : ∑ m, (L ^ (n + 1)) l m = ∑ k, L l k * ∑ m, (L ^ n) k m := by
        rw [pow_succ']
        simp only [Matrix.mul_apply]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
      have hsn : s ^ n ≠ 0 := pow_ne_zero _ hs.ne'
      show ∑ k, L l k * ((∑ m, (L ^ n) k m) / s ^ n) = s * ((∑ m, (L ^ (n + 1)) l m) / s ^ (n + 1))
      rw [e]
      have h1 : ∑ k, L l k * ((∑ m, (L ^ n) k m) / s ^ n) =
          (∑ k, L l k * ∑ m, (L ^ n) k m) / s ^ n := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [h1, pow_succ]; field_simp
    have e1 : (L *ᵥ v) l = ∑' n, ∑ k, L l k * t n k := by
      simp only [Matrix.mulVec, dotProduct, hv]
      rw [Summable.tsum_finsetSum (f := fun k n => L l k * t n k) (s := Finset.univ) (fun k _ => (hsum k).mul_left _)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [tsum_mul_left]
    rw [e1]
    simp only [hshift]
    rw [tsum_mul_left]
    apply mul_le_mul_of_nonneg_left _ hs.le
    rw [hv]
    simp only
    rw [(hsum l).tsum_eq_zero_add]
    linarith [htnn 0 l]
  -- the weighted sup norm
  let D : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun x l => x l / v l
      map_add' := fun x y => by funext l; simp [add_div]
      map_smul' := fun c x => by funext l; simp [mul_div_assoc] }
  let ν : Seminorm ℝ (ι → ℝ) := (normSeminorm ℝ (ι → ℝ)).comp D
  have hν : ∀ x, ν x = ‖fun l => x l / v l‖ := fun x => rfl
  have hcoord : ∀ x l, |x l| ≤ ν x * v l := by
    intro x l
    have h := norm_le_pi_norm (fun l => x l / v l) l
    rw [← hν, Real.norm_eq_abs, abs_div, abs_of_pos (hvpos l), div_le_iff₀ (hvpos l)] at h
    exact h
  refine ⟨ν, ?_, ?_, ?_⟩
  · intro x hx
    rw [hν, norm_eq_zero] at hx
    funext l
    have := congrFun hx l
    simp only [Pi.zero_apply, div_eq_zero_iff] at this
    rcases this with h | h
    · exact h
    · exact absurd h (hvpos l).ne'
  · intro x
    rw [hν, hν]
    -- norms of the two vectors coincide coordinatewise
    apply le_antisymm
    · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun l => ?_)
      have := norm_le_pi_norm (fun l => |x l| / v l) l
      simp only [Real.norm_eq_abs, abs_div, abs_abs] at this ⊢
      exact this
    · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun l => ?_)
      have := norm_le_pi_norm (fun l => x l / v l) l
      simp only [Real.norm_eq_abs, abs_div, abs_abs] at this ⊢
      exact this
  · intro x
    have key : ν (L *ᵥ x) ≤ s * ν x := by
      rw [hν]
      refine (pi_norm_le_iff_of_nonneg (by have := apply_nonneg ν x; positivity)).2 (fun l => ?_)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (hvpos l), div_le_iff₀ (hvpos l)]
      calc |(L *ᵥ x) l| ≤ ∑ m, L l m * |x m| := by
            simp only [Matrix.mulVec, dotProduct]
            refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
            refine Finset.sum_congr rfl (fun m _ => ?_)
            rw [abs_mul, abs_of_nonneg (hL l m)]
        _ ≤ ∑ m, L l m * (ν x * v m) :=
            Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left (hcoord x m) (hL l m))
        _ = ν x * (L *ᵥ v) l := by
            simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun m _ => ?_); ring
        _ ≤ ν x * (s * v l) := mul_le_mul_of_nonneg_left (hLv l) (apply_nonneg ν x)
        _ = s * ν x * v l := by ring
    have hsρ : ENNReal.ofReal s = ρ + ENNReal.ofReal ε := by
      rw [hρr, ← ENNReal.ofReal_add hr0 hε.le]
    calc ENNReal.ofReal (ν (L *ᵥ x)) ≤ ENNReal.ofReal (s * ν x) := ENNReal.ofReal_le_ofReal key
      _ = ENNReal.ofReal s * ENNReal.ofReal (ν x) := ENNReal.ofReal_mul hs.le
      _ = _ := by rw [hsρ]
