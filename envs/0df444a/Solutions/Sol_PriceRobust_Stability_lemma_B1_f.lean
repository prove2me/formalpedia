-- Prove2me | solution 1 for PriceRobust.Stability.lemma_B1_f
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T20:22:34.382994+00:00
-- url     : https://prove2.me/submissions/09591452-e3bc-4986-b4a4-1e242df5b86f

import Mathlib
import Definitions.Def_PriceRobust_Stability_ZPMatrix

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

end PRB1

namespace PRB1
open PriceRobust.Stability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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

lemma split_sum {n : Type*} [Fintype n] [DecidableEq n] (S : Finset n) (f : n → ℝ) :
    ∑ l : {l // l ∈ S}, f l + ∑ l : {l // l ∉ S}, f l = ∑ l, f l := by
  rw [← Finset.sum_add_sum_compl S f, Finset.sum_coe_sort S f]
  congr 1
  exact (Finset.sum_subtype Sᶜ (fun x => by simp) f).symm

open PriceRobust.Stability in
theorem solution {n : Type*} [Fintype n] [DecidableEq n]
    (Y X : Matrix n n ℝ) (S : Finset n)
    (hsymm : Y.IsSymm) (hY : IsZPMatrix Y) (hX : X = Y⁻¹) :
    ∀ l m, 0 ≤ (X.submatrix (fun x : {l // l ∉ S} => x.1) (fun x : {l // l ∈ S} => x.1) *
        (X.submatrix (fun x : {l // l ∈ S} => x.1) (fun x : {l // l ∈ S} => x.1))⁻¹ *
        X.submatrix (fun x : {l // l ∈ S} => x.1) (fun x : {l // l ∉ S} => x.1)) l m := by
  obtain ⟨hYu, hYinv⟩ := PRB1.inv_nonneg Y Y hY hY.1 (fun _ _ => le_rfl)
  have hXnn : ∀ l m, 0 ≤ X l m := by rw [hX]; exact hYinv
  have hYX : Y * X = 1 := by rw [hX]; exact Matrix.mul_nonsing_inv Y hYu
  set X11 := X.submatrix (fun x : {l // l ∈ S} => x.1) (fun x : {l // l ∈ S} => x.1)
  set X12 := X.submatrix (fun x : {l // l ∈ S} => x.1) (fun x : {l // l ∉ S} => x.1)
  set X21 := X.submatrix (fun x : {l // l ∉ S} => x.1) (fun x : {l // l ∈ S} => x.1)
  set Y21 := Y.submatrix (fun x : {l // l ∉ S} => x.1) (fun x : {l // l ∈ S} => x.1)
  set Y22 := Y.submatrix (fun x : {l // l ∉ S} => x.1) (fun x : {l // l ∉ S} => x.1)
  have hY22 : IsZPMatrix Y22 := PRB1.ZP_sub Y hY (fun l => l ∉ S)
  obtain ⟨hY22u, hY22inv⟩ := PRB1.inv_nonneg Y22 Y22 hY22 hY22.1 (fun _ _ => le_rfl)
  -- block identity: Y21 X11 + Y22 X21 = 0
  have hblk : Y21 * X11 + Y22 * X21 = 0 := by
    ext i j
    have hne : i.1 ≠ j.1 := fun h => i.2 (h ▸ j.2)
    have h := congrFun (congrFun hYX i.1) j.1
    rw [Matrix.one_apply_ne hne, Matrix.mul_apply] at h
    rw [← split_sum S] at h
    simpa [X11, X21, Y21, Y22, Matrix.add_apply, Matrix.mul_apply] using h
  have hX21 : X21 = -(Y22⁻¹ * Y21 * X11) := by
    have h2 : Y22 * X21 = -(Y21 * X11) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hblk
    calc X21 = Y22⁻¹ * (Y22 * X21) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Y22 hY22u, Matrix.one_mul]
      _ = _ := by rw [h2, Matrix.mul_neg, Matrix.mul_assoc]
  have hY21 : ∀ a b, Y21 a b ≤ 0 := fun a b => hY.1 a.1 b.1 (fun h => a.2 (h ▸ b.2))
  intro l m
  by_cases hu : IsUnit X11.det
  · have e : X21 * X11⁻¹ * X12 = -(Y22⁻¹ * Y21 * X12) := by
      rw [hX21, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc (Y22⁻¹ * Y21) X11,
        Matrix.mul_nonsing_inv X11 hu, Matrix.mul_one]
    rw [e, Matrix.neg_apply, Matrix.mul_apply, ← Finset.sum_neg_distrib]
    apply Finset.sum_nonneg
    intro b _
    rw [Matrix.mul_apply, Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_nonneg
    intro a _
    have h1 := hY22inv l a
    have h2 := hY21 a b
    have h3 : 0 ≤ X12 b m := hXnn _ _
    have : 0 ≤ Y22⁻¹ l a * (-Y21 a b) * X12 b m := by
      apply mul_nonneg (mul_nonneg h1 (by linarith)) h3
    linarith
  · rw [Matrix.nonsing_inv_apply_not_isUnit X11 hu]
    simp
