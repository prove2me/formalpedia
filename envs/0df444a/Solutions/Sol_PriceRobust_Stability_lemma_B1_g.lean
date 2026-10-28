-- Prove2me | solution 1 for PriceRobust.Stability.lemma_B1_g
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T20:16:26.237452+00:00
-- url     : https://prove2.me/submissions/fe3b4faa-e89b-4676-ae78-96d9970167e9

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

open PriceRobust.Stability in
theorem solution {n : Type*} [Fintype n] [DecidableEq n]
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
    have hle := PRB1.mono _ rfl (1 - Q) hA (-w) hneg
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
