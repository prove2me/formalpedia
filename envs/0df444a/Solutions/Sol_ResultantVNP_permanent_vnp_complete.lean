-- Prove2me | solution 1 for ResultantVNP.permanent_vnp_complete
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T21:25:56.149748+00:00
-- url     : https://prove2.me/submissions/556a1dfa-45bf-452f-86f3-bdbf4d61945d

import Definitions.Def_ResultantVNP_FormulaWitness
import Definitions.Def_ResultantVNP_IsProjection
import Definitions.Def_ResultantVNP_IsVNPHardPProj
import Mathlib
import Theorems.Thm_ResultantVNP_vp_formula_sum


-- BEGIN Solutions.PermanentBlocks
/-
Copyright (c) 2026 Kenny Lau, Chris Hughes, Anne Baanen, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Anne Baanen, Samuel Schlesinger
-/



/- Adapted for Lean 4.33.1 from cslib-frontier revision
e78796a1e0c0fe124f9130a84850a5104bbe5f14,
CslibFrontier/Foundations/Data/Matrix/Permanent/Blocks.lean.
Source: https://github.com/cslib-community/cslib-frontier -/

namespace Matrix

open Equiv Equiv.Perm Finset Fintype

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {R : Type*} [CommSemiring R]

/-- Reindexing both rows and columns of a square matrix by the same equivalence preserves its
permanent. -/
@[simp] theorem permanent_submatrix_equiv {m' : Type*} [Fintype m'] [DecidableEq m'] (e : m' ≃ m)
    (A : Matrix m m R) : (A.submatrix e e).permanent = A.permanent := by
  rw [permanent, permanent, ← (Equiv.permCongr e).sum_comp]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← e.prod_comp]
  exact Finset.prod_congr rfl fun i _ => by simp [submatrix_apply, Equiv.permCongr_apply]

/-- Reindexing the rows and columns of a square matrix by any two equivalences preserves its
permanent. -/
theorem permanent_submatrix_equiv_equiv {m' : Type*} [Fintype m'] [DecidableEq m']
    (e₁ e₂ : m' ≃ m) (A : Matrix m m R) : (A.submatrix e₁ e₂).permanent = A.permanent := by
  have h : A.submatrix e₁ e₂ = (A.submatrix e₂ e₂).submatrix (e₁.trans e₂.symm) id := by
    ext i j
    simp [submatrix_apply]
  rw [h, permanent_permute_cols, permanent_submatrix_equiv]

/-- Multilinearity of the permanent in a column. -/
@[simp] theorem permanent_updateCol_add (M : Matrix m m R) (j : m) (u v : m → R) :
    (M.updateCol j (u + v)).permanent =
      (M.updateCol j u).permanent + (M.updateCol j v).permanent := by
  simp only [permanent, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), updateCol_self,
    Pi.add_apply, add_mul, Finset.sum_add_distrib]
  congr 1 <;>
    refine Finset.sum_congr rfl fun p _ =>
      congrArg (_ * ·) (Finset.prod_congr rfl fun i hi => ?_) <;>
    simp only [ne_eq, Finset.ne_of_mem_erase hi, not_false_eq_true, updateCol_ne]

/-- Multilinearity of the permanent in a row. -/
@[simp] theorem permanent_updateRow_add (M : Matrix m m R) (i : m) (u v : m → R) :
    (M.updateRow i (u + v)).permanent =
      (M.updateRow i u).permanent + (M.updateRow i v).permanent := by
  rw [← permanent_transpose, ← updateCol_transpose, permanent_updateCol_add,
    updateCol_transpose, updateCol_transpose, permanent_transpose, permanent_transpose]

/-- If two matrices `M₁, M₂` agree with `M` outside row `r` and their `r`-th rows sum to row `r`
of `M`, then `M.permanent = M₁.permanent + M₂.permanent`. -/
theorem permanent_add_of_row_eq (M M₁ M₂ : Matrix m m R) (r : m)
    (hr : ∀ j, M r j = M₁ r j + M₂ r j)
    (h₁ : ∀ i ≠ r, ∀ j, M₁ i j = M i j)
    (h₂ : ∀ i ≠ r, ∀ j, M₂ i j = M i j) :
    M.permanent = M₁.permanent + M₂.permanent := by
  have hM : M = M.updateRow r (M₁ r + M₂ r) := by
    ext i j
    by_cases hir : i = r
    · subst hir; simp [hr j]
    · simp [hir]
  have hM₁ : M₁ = M.updateRow r (M₁ r) := by
    ext i j
    by_cases hir : i = r
    · subst hir; simp
    · simp [hir, h₁ i hir j]
  have hM₂ : M₂ = M.updateRow r (M₂ r) := by
    ext i j
    by_cases hir : i = r
    · subst hir; simp
    · simp [hir, h₂ i hir j]
  conv_lhs => rw [hM]
  rw [permanent_updateRow_add, ← hM₁, ← hM₂]

/-- Applying a ring homomorphism to the permanent of a matrix is the permanent of the mapped
matrix. -/
theorem _root_.RingHom.map_permanent {S : Type*} [CommSemiring S] (f : R →+* S)
    (M : Matrix m m R) : f M.permanent = (M.map f).permanent := by
  simp [permanent, map_sum, map_prod]

/-- Applying an algebra homomorphism to the permanent of a matrix is the permanent of the mapped
matrix. -/
theorem _root_.AlgHom.map_permanent {R₀ A B : Type*} [CommSemiring R₀] [CommSemiring A]
    [CommSemiring B] [Algebra R₀ A] [Algebra R₀ B] (f : A →ₐ[R₀] B) (M : Matrix m m A) :
    f M.permanent = (M.map f).permanent :=
  f.toRingHom.map_permanent M

/-- The permanent of a `2 × 2` block matrix with the lower-left block equal to zero is the product
of the permanents of the diagonal blocks. -/
@[simp] theorem permanent_fromBlocks_zero₂₁ (A : Matrix m m R) (B : Matrix m n R)
    (D : Matrix n n R) : (fromBlocks A B 0 D).permanent = A.permanent * D.permanent := by
  classical
  simp_rw [permanent]
  convert
    Eq.symm <|
      sum_subset (M := R) (subset_univ ((sumCongrHom m n).range : Set (Perm (m ⊕ n))).toFinset) ?_
  · simp_rw [Finset.sum_mul_sum, ← sum_product', univ_product_univ]
    refine sum_nbij (fun σ => σ.fst.sumCongr σ.snd) ?_ ?_ ?_ ?_
    · intro σ₁₂ _
      exact Set.mem_toFinset.mpr ⟨σ₁₂, rfl⟩
    · intro σ₁ _ σ₂ _ h
      have h2 : ∀ x, Perm.sumCongr σ₁.fst σ₁.snd x = Perm.sumCongr σ₂.fst σ₂.snd x :=
        DFunLike.congr_fun h
      simp only [Sum.map_inr, Sum.map_inl, Perm.sumCongr_apply, Sum.forall, Sum.inl.injEq,
        Sum.inr.injEq] at h2
      ext x
      · exact h2.left x
      · exact h2.right x
    · intro σ hσ
      rw [mem_coe, Set.mem_toFinset] at hσ
      obtain ⟨σ₁₂, hσ₁₂⟩ := hσ
      exact ⟨σ₁₂, mem_univ _, by simpa using hσ₁₂⟩
    · simp only [forall_prop_of_true, Prod.forall, mem_univ]
      intro σ₁ σ₂
      rw [Fintype.prod_sum_type]
      simp_rw [Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, fromBlocks_apply₁₁,
        fromBlocks_apply₂₂]
  · rintro σ - hσn
    have h1 : ¬∀ x, ∃ y, Sum.inl y = σ (Sum.inl x) := by
      rw [Set.mem_toFinset] at hσn
      simpa only [Set.MapsTo, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] using
        mt mem_sumCongrHom_range_of_perm_mapsTo_inl hσn
    obtain ⟨a, ha⟩ := not_forall.mp h1
    rcases hx : σ (Sum.inl a) with a2 | b
    · exact absurd hx.symm ((not_exists.mp ha) a2)
    · rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a))]
      rw [hx, fromBlocks_apply₂₁, Matrix.zero_apply]

/-- The permanent of a `2 × 2` block matrix with the upper-right block equal to zero is the product
of the permanents of the diagonal blocks. -/
@[simp] theorem permanent_fromBlocks_zero₁₂ (A : Matrix m m R) (C : Matrix n m R)
    (D : Matrix n n R) : (fromBlocks A 0 C D).permanent = A.permanent * D.permanent := by
  rw [← permanent_transpose, fromBlocks_transpose, transpose_zero, permanent_fromBlocks_zero₂₁,
    permanent_transpose, permanent_transpose]

/-- The permanent of a block-diagonal `2 × 2` matrix is the product of the permanents of its
diagonal blocks. -/
theorem permanent_fromBlocks_zero (A : Matrix m m R) (D : Matrix n n R) :
    (fromBlocks A (0 : Matrix m n R) 0 D).permanent = A.permanent * D.permanent :=
  permanent_fromBlocks_zero₂₁ A 0 D

end Matrix


-- BEGIN Solutions.PermanentSplit
/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/



/- Adapted for Lean 4.33.1 from cslib-frontier e78796a1e0c0fe124f9130a84850a5104bbe5f14,
CslibFrontier/Foundations/Data/Matrix/Permanent/Split.lean. -/

open Finset

namespace Matrix

variable {V R : Type*} [Fintype V] [DecidableEq V] [CommSemiring R]

open Classical in
/-- The functions mapping `S` bijectively onto `T` and fixing every index outside `S`. -/
noncomputable def bijOn (S T : Finset V) : Finset (V → V) :=
  univ.filter fun f => (∀ i ∈ S, f i ∈ T) ∧ (∀ i ∈ S, ∀ j ∈ S, f i = f j → i = j) ∧
    (∀ t ∈ T, ∃ i ∈ S, f i = t) ∧ ∀ i ∉ S, f i = i

theorem mem_bijOn {S T : Finset V} {f : V → V} :
    f ∈ bijOn S T ↔ (∀ i ∈ S, f i ∈ T) ∧ (∀ i ∈ S, ∀ j ∈ S, f i = f j → i = j) ∧
      (∀ t ∈ T, ∃ i ∈ S, f i = t) ∧ ∀ i ∉ S, f i = i := by
  classical
  simp [bijOn]

/-- A bijection between two finite index sets forces equal cardinalities. -/
theorem card_eq_of_mem_bijOn {S T : Finset V} {f : V → V} (hf : f ∈ bijOn S T) :
    S.card = T.card := by
  obtain ⟨hm,hi,hs,_⟩ := mem_bijOn.mp hf
  exact Finset.card_bij (fun i _ => f i) (fun i hi' => hm i hi')
    (fun i hi' j hj' hij => hi i hi' j hj' hij) (by
      intro j hj
      obtain ⟨i,his,hij⟩ := hs j hj
      exact ⟨i,his,hij⟩)

/-- The permanent sum between the row set `S` and the column set `T`: the sum over bijections
`f` from `S` onto `T` of `∏ i ∈ S, M i (f i)`. -/
noncomputable def permOn (M : Matrix V V R) (S T : Finset V) : R :=
  ∑ f ∈ bijOn S T, ∏ i ∈ S, M i (f i)

/-- A rectangular minor with unequal numbers of rows and columns vanishes. -/
theorem permOn_eq_zero_of_card_ne (M : Matrix V V R) (S T : Finset V)
    (h : S.card ≠ T.card) : permOn M S T = 0 := by
  unfold permOn
  apply Finset.sum_eq_zero
  intro f hf
  exact (h (card_eq_of_mem_bijOn hf)).elim

/-- The permanent is the permanent sum between all rows and all columns. -/
theorem permanent_eq_permOn (M : Matrix V V R) : M.permanent = permOn M univ univ := by
  rw [← permanent_transpose, permanent, permOn]
  simp only [transpose_apply]
  refine Finset.sum_bij' (fun σ _ => ⇑σ)
    (fun f hf => Equiv.ofBijective f ?_) (fun σ _ => ?_) (fun f hf => mem_univ _)
    (fun σ _ => ?_) (fun f hf => ?_) (fun σ _ => rfl)
  · obtain ⟨-, hinj, hsurj, -⟩ := mem_bijOn.1 hf
    exact ⟨fun i j h => hinj i (mem_univ _) j (mem_univ _) h,
      fun t => let ⟨i, _, hi⟩ := hsurj t (mem_univ _); ⟨i, hi⟩⟩
  · exact mem_bijOn.2 ⟨fun _ _ => mem_univ _, fun i _ j _ h => σ.injective h,
      fun t _ => ⟨σ.symm t, mem_univ _, σ.apply_symm_apply t⟩, fun i hi => absurd (mem_univ i) hi⟩
  · ext; rfl
  · rfl

/-- The permanent sum depends only on the entries in rows `S` and columns `T`. -/
theorem permOn_congr {M N : Matrix V V R} {S T : Finset V}
    (h : ∀ i ∈ S, ∀ j ∈ T, M i j = N i j) : permOn M S T = permOn N S T := by
  refine Finset.sum_congr rfl fun f hf => Finset.prod_congr rfl fun i hi => ?_
  exact h i hi (f i) ((mem_bijOn.1 hf).1 i hi)

/-- A row of `S` vanishing on the columns `T` makes the permanent sum vanish. -/
theorem permOn_eq_zero_of_row {M : Matrix V V R} {S T : Finset V} {i : V} (hi : i ∈ S)
    (h : ∀ j ∈ T, M i j = 0) : permOn M S T = 0 :=
  Finset.sum_eq_zero fun _ hf =>
    Finset.prod_eq_zero hi (h _ ((mem_bijOn.1 hf).1 i hi))

/-- A column of `T` vanishing on the rows `S` makes the permanent sum vanish. -/
theorem permOn_eq_zero_of_col {M : Matrix V V R} {S T : Finset V} {j : V} (hj : j ∈ T)
    (h : ∀ i ∈ S, M i j = 0) : permOn M S T = 0 :=
  Finset.sum_eq_zero fun f hf => by
    obtain ⟨i, hi, rfl⟩ := (mem_bijOn.1 hf).2.2.1 j hj
    exact Finset.prod_eq_zero hi (h i hi)

/-- There is one bijection between empty sets. -/
theorem permOn_empty_left (M : Matrix V V R) (T : Finset V) :
    permOn M ∅ T = if T = ∅ then 1 else 0 := by
  rw [permOn]
  split_ifs with hT
  · subst hT
    have : bijOn (∅ : Finset V) ∅ = {id} := by
      ext f
      simp only [mem_bijOn, notMem_empty, IsEmpty.forall_iff, implies_true, false_and,
        exists_false, not_false_eq_true, forall_const, true_and, mem_singleton]
      exact ⟨fun h => funext h, fun h i => h ▸ rfl⟩
    rw [this, sum_singleton, prod_empty]
  · obtain ⟨t, ht⟩ := nonempty_iff_ne_empty.2 hT
    refine sum_eq_zero fun f hf => ?_
    obtain ⟨i, hi, -⟩ := (mem_bijOn.1 hf).2.2.1 t ht
    exact absurd hi (notMem_empty i)

/-- Restrict a function to `X`: equal to `f` on `X`, the identity elsewhere. -/
private def restrictTo (X : Finset V) (f : V → V) : V → V :=
  fun i => if i ∈ X then f i else i

/-- Glue two functions along `X`. -/
private def glue (X : Finset V) (f₁ f₂ : V → V) : V → V :=
  fun i => if i ∈ X then f₁ i else f₂ i

/-- **Generalized Laplace expansion** along a set `S' ⊆ S` of rows. -/
theorem permOn_split (M : Matrix V V R) {S S' : Finset V} (hS' : S' ⊆ S) (T : Finset V) :
    permOn M S T =
      ∑ T' ∈ T.powerset, permOn M S' T' * permOn M (S \ S') (T \ T') := by
  have hR : ∑ T' ∈ T.powerset, permOn M S' T' * permOn M (S \ S') (T \ T') =
      ∑ x ∈ T.powerset.sigma fun T' => bijOn S' T' ×ˢ bijOn (S \ S') (T \ T'),
        (∏ i ∈ S', M i (x.2.1 i)) * ∏ i ∈ S \ S', M i (x.2.2 i) := by
    rw [sum_sigma]
    refine sum_congr rfl fun T' _ => ?_
    rw [permOn, permOn, sum_mul_sum, sum_product]
  rw [hR, permOn]
  symm
  refine Finset.sum_bij' (fun x _ => glue S' x.2.1 x.2.2)
    (fun f _ => ⟨S'.image f, restrictTo S' f, restrictTo (S \ S') f⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨T', f₁, f₂⟩ hx
    simp only [mem_sigma, mem_powerset, mem_product, mem_bijOn] at hx
    obtain ⟨hT', ⟨h₁m, h₁i, h₁s, h₁o⟩, ⟨h₂m, h₂i, h₂s, h₂o⟩⟩ := hx
    refine mem_bijOn.2 ⟨fun i hi => ?_, fun i hi j hj h => ?_, fun t ht => ?_, fun i hi => ?_⟩
    · simp only [glue]
      split_ifs with h
      · exact hT' (h₁m i h)
      · exact (mem_sdiff.1 (h₂m i (mem_sdiff.2 ⟨hi, h⟩))).1
    · simp only [glue] at h
      by_cases hi' : i ∈ S' <;> by_cases hj' : j ∈ S' <;> simp only [hi', hj', ite_true,
        ite_false] at h
      · exact h₁i i hi' j hj' h
      · exact absurd (h ▸ h₁m i hi') (mem_sdiff.1 (h₂m j (mem_sdiff.2 ⟨hj, hj'⟩))).2
      · exact absurd (h ▸ h₁m j hj') (mem_sdiff.1 (h₂m i (mem_sdiff.2 ⟨hi, hi'⟩))).2
      · exact h₂i i (mem_sdiff.2 ⟨hi, hi'⟩) j (mem_sdiff.2 ⟨hj, hj'⟩) h
    · by_cases htT : t ∈ T'
      · obtain ⟨i, hi, rfl⟩ := h₁s t htT
        exact ⟨i, hS' hi, by simp [glue, hi]⟩
      · obtain ⟨i, hi, rfl⟩ := h₂s _ (mem_sdiff.2 ⟨ht, htT⟩)
        exact ⟨i, (mem_sdiff.1 hi).1, by simp [glue, (mem_sdiff.1 hi).2]⟩
    · have hi' : i ∉ S' := fun h => hi (hS' h)
      simp only [glue, hi', ite_false]
      exact h₂o i fun h => hi (mem_sdiff.1 h).1
  · intro f hf
    obtain ⟨hm, hi, hs, ho⟩ := mem_bijOn.1 hf
    simp only [mem_sigma, mem_powerset, mem_product, mem_bijOn, restrictTo]
    refine ⟨fun t ht => ?_, ⟨fun i hi' => ?_, fun i hi' j hj' h => ?_, fun t ht => ?_,
      fun i hi' => ?_⟩, ⟨fun i hi' => ?_, fun i hi' j hj' h => ?_, fun t ht => ?_,
      fun i hi' => ?_⟩⟩
    · obtain ⟨i, hi', rfl⟩ := mem_image.1 ht
      exact hm i (hS' hi')
    · simp only [hi', ite_true]; exact mem_image_of_mem f hi'
    · simp only [hi', hj', ite_true] at h; exact hi i (hS' hi') j (hS' hj') h
    · obtain ⟨i, hi', rfl⟩ := mem_image.1 ht
      exact ⟨i, hi', by simp [hi']⟩
    · simp [hi']
    · simp only [hi', ite_true]
      refine mem_sdiff.2 ⟨hm i (mem_sdiff.1 hi').1, fun h => ?_⟩
      obtain ⟨j, hj, hji⟩ := mem_image.1 h
      exact (mem_sdiff.1 hi').2 (hi j (hS' hj) i (mem_sdiff.1 hi').1 hji ▸ hj)
    · simp only [hi', hj', ite_true] at h
      exact hi i (mem_sdiff.1 hi').1 j (mem_sdiff.1 hj').1 h
    · obtain ⟨i, hi', rfl⟩ := hs t (mem_sdiff.1 ht).1
      refine ⟨i, mem_sdiff.2 ⟨hi', fun h => (mem_sdiff.1 ht).2 (mem_image_of_mem f h)⟩, ?_⟩
      simp [mem_sdiff.2 ⟨hi', fun h => (mem_sdiff.1 ht).2 (mem_image_of_mem f h)⟩]
    · simp [hi']
  · rintro ⟨T', f₁, f₂⟩ hx
    simp only [mem_sigma, mem_powerset, mem_product, mem_bijOn] at hx
    obtain ⟨hT', ⟨h₁m, h₁i, h₁s, h₁o⟩, ⟨h₂m, h₂i, h₂s, h₂o⟩⟩ := hx
    have himg : S'.image (glue S' f₁ f₂) = T' := by
      ext t
      simp only [mem_image, glue]
      constructor
      · rintro ⟨i, hi, rfl⟩; simp only [hi, ite_true]; exact h₁m i hi
      · intro ht
        obtain ⟨i, hi, rfl⟩ := h₁s t ht
        exact ⟨i, hi, by simp [hi]⟩
    simp only [Sigma.mk.injEq, himg, true_and]
    refine heq_of_eq (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
    · simp only [restrictTo, glue]
      split_ifs with h
      · rfl
      · exact (h₁o i h).symm
    · simp only [restrictTo, glue]
      by_cases h : i ∈ S'
      · simp only [h, ite_true, mem_sdiff, not_true_eq_false, and_false, ite_false]
        exact (h₂o i fun h' => (mem_sdiff.1 h').2 h).symm
      · by_cases h' : i ∈ S
        · simp [h, h']
        · simp only [h, ite_false, mem_sdiff, h', false_and]
          exact (h₂o i fun h'' => h' (mem_sdiff.1 h'').1).symm
  · intro f hf
    obtain ⟨-, -, -, ho⟩ := mem_bijOn.1 hf
    funext i
    simp only [glue, restrictTo]
    by_cases h : i ∈ S'
    · simp [h]
    · by_cases h' : i ∈ S
      · simp [h, h']
      · simp [h, h', ho i h']
  · rintro ⟨T', f₁, f₂⟩ -
    rw [← prod_sdiff hS', mul_comm]
    congr 1
    · exact prod_congr rfl fun i hi => by simp [glue, (mem_sdiff.1 hi).2]
    · exact prod_congr rfl fun i hi => by simp [glue, hi]

open Classical in
/-- **The permanent sum of a sum of two matrices**: choose the rows `S'` taken from `A`, the
columns `T'` they are matched to, and match the remaining rows and columns in `C`. -/
theorem permOn_add (A C : Matrix V V R) (S T : Finset V) :
    permOn (A + C) S T =
      ∑ S' ∈ S.powerset, ∑ T' ∈ T.powerset, permOn A S' T' * permOn C (S \ S') (T \ T') := by
  have hexp : permOn (A + C) S T = ∑ S' ∈ S.powerset,
      permOn (Matrix.of fun i j => if i ∈ S' then A i j else C i j) S T := by
    rw [permOn]
    simp only [Matrix.add_apply, prod_add, permOn, of_apply]
    rw [sum_comm]
    refine sum_congr rfl fun S' hS' => sum_congr rfl fun f _ => ?_
    rw [← prod_sdiff (mem_powerset.1 hS'), mul_comm]
    congr 1
    · exact prod_congr rfl fun i hi => by simp [(mem_sdiff.1 hi).2]
    · exact prod_congr rfl fun i hi => by simp [hi]
  rw [hexp]
  refine sum_congr rfl fun S' hS' => ?_
  rw [permOn_split _ (mem_powerset.1 hS')]
  refine sum_congr rfl fun T' _ => ?_
  congr 1
  · exact permOn_congr fun i hi j _ => by simp [hi]
  · exact permOn_congr fun i hi j _ => by simp [(mem_sdiff.1 hi).2]

/-- The permanent sum from one row to one column is the entry. -/
theorem permOn_singleton (M : Matrix V V R) (i j : V) : permOn M {i} {j} = M i j := by
  rw [permOn]
  have : bijOn ({i} : Finset V) {j} = {Function.update id i j} := by
    ext f
    simp only [mem_bijOn, mem_singleton, forall_eq, exists_eq_left]
    constructor
    · rintro ⟨h1, -, -, h4⟩
      funext k
      by_cases hk : k = i
      · subst hk; simp [h1]
      · simp [Function.update, hk, h4 k hk]
    · rintro rfl
      exact ⟨by simp, by simp, by simp, fun k hk => by simp [Function.update, hk]⟩
  rw [this, sum_singleton, prod_singleton, Function.update_self]

/-- The permanent sum from one row to a set of columns that is not a singleton vanishes. -/
theorem permOn_singleton_left_eq_zero (M : Matrix V V R) (i : V) {T : Finset V}
    (hT : ∀ j, T ≠ {j}) : permOn M {i} T = 0 := by
  rw [permOn]
  refine sum_eq_zero fun f hf => absurd ?_ (hT (f i))
  obtain ⟨hm, -, hs, -⟩ := mem_bijOn.1 hf
  ext t
  simp only [mem_singleton]
  refine ⟨fun ht => ?_, fun ht => ht ▸ hm i (mem_singleton_self i)⟩
  obtain ⟨k, hk, rfl⟩ := hs t ht
  rw [mem_singleton.1 hk]

/-- **Laplace expansion of the permanent sum** along a row `i ∈ S`. -/
theorem permOn_laplace (M : Matrix V V R) {S : Finset V} {i : V} (hi : i ∈ S) (T : Finset V) :
    permOn M S T = ∑ j ∈ T, M i j * permOn M (S.erase i) (T.erase j) := by
  rw [permOn_split M (singleton_subset_iff.2 hi) T]
  have hsub : T.image (fun j => ({j} : Finset V)) ⊆ T.powerset := fun T' hT' => by
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hT'
    exact mem_powerset.2 (singleton_subset_iff.2 hj)
  rw [← sum_subset hsub ?zero, sum_image fun _ _ _ _ h => singleton_injective h]
  · refine sum_congr rfl fun j _ => ?_
    rw [permOn_singleton, sdiff_singleton_eq_erase, sdiff_singleton_eq_erase]
  case zero =>
    intro T' hT' hn
    rw [permOn_singleton_left_eq_zero M i fun j hj => hn (mem_image.2 ⟨j, ?_, hj.symm⟩),
      zero_mul]
    exact singleton_subset_iff.1 (hj ▸ mem_powerset.1 hT')

/-- If a column has only one possible nonzero row, that edge is forced. -/
theorem permOn_forced_column (M : Matrix V V R) {S T : Finset V} {i j : V}
    (hi : i ∈ S) (hj : j ∈ T) (hzero : ∀ k ∈ S, k ≠ i → M k j = 0) :
    permOn M S T = M i j * permOn M (S.erase i) (T.erase j) := by
  rw [permOn_laplace M hi T]
  apply Finset.sum_eq_single j
  · intro k hk hkj
    have hmem : j ∈ T.erase k := Finset.mem_erase.mpr ⟨hkj.symm,hj⟩
    have hz : permOn M (S.erase i) (T.erase k) = 0 :=
      permOn_eq_zero_of_col hmem (fun r hr => hzero r (Finset.mem_erase.mp hr).2
        (Finset.mem_erase.mp hr).1)
    rw [hz,mul_zero]
  · intro hn
    exact (hn hj).elim

/-- Changing a zero diagonal entry to one adds the corresponding principal minor. -/
theorem permOn_set_diagonal_one (M : Matrix V V R) (S : Finset V) (i : V)
    (hi : i ∈ S) (hzero : M i i = 0) :
    permOn (M.updateRow i (Function.update (M i) i 1)) S S =
      permOn M S S + permOn M (S.erase i) (S.erase i) := by
  let N := M.updateRow i (Function.update (M i) i 1)
  have hminor (j : V) : permOn N (S.erase i) (S.erase j) =
      permOn M (S.erase i) (S.erase j) := by
    apply permOn_congr
    intro k hk l hl
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    simp [N,Matrix.updateRow_ne hki]
  rw [permOn_laplace N hi S,permOn_laplace M hi S]
  simp_rw [hminor]
  have hentry (j : V) : N i j = M i j + if j = i then 1 else 0 := by
    by_cases h : j = i
    · subst j; simp [N,hzero]
    · simp [N,h]
  simp_rw [hentry,add_mul,Finset.sum_add_distrib]
  congr 1
  simp [hi]

/-- Laplace expansion along explicit lists of rows and columns: the rows are expanded in list
order, each matched to a remaining column. -/
def permOnList {V R : Type*} [DecidableEq V] [CommSemiring R] (M : V → V → R) :
    List V → List V → R
  | [], [] => 1
  | [], _ :: _ => 0
  | i :: is, cols => (cols.map fun j => M i j * permOnList M is (cols.erase j)).sum

/-- Relabeling rows and columns injectively preserves the list expansion. -/
theorem permOnList_map {A B R : Type*} [DecidableEq A] [DecidableEq B] [CommSemiring R]
    (f : A → B) (hf : Function.Injective f) (M : B → B → R) (rows cols : List A) :
    permOnList M (rows.map f) (cols.map f) =
      permOnList (fun i j => M (f i) (f j)) rows cols := by
  induction rows generalizing cols with
  | nil => cases cols <;> rfl
  | cons i is ih =>
    simp only [List.map_cons,permOnList,List.map_map,Function.comp_apply]
    congr 1
    apply List.map_congr_left
    intro j hj
    simp only [Function.comp_apply]
    rw [← List.map_erase hf,ih]

/-- `permOn` is evaluated by `permOnList` on duplicate-free lists of its rows and columns. -/
theorem permOn_eq_permOnList (M : Matrix V V R) (rows cols : List V) (hr : rows.Nodup)
    (hc : cols.Nodup) : permOn M rows.toFinset cols.toFinset = permOnList M rows cols := by
  induction rows generalizing cols with
  | nil =>
    rw [List.toFinset_nil, permOn_empty_left]
    cases cols with
    | nil => simp [permOnList]
    | cons j js => simp [permOnList]
  | cons i is ih =>
    have hi : i ∈ (i :: is).toFinset := by simp
    simp only [permOnList]
    rw [permOn_laplace M hi, ← List.sum_toFinset _ hc]
    · refine sum_congr rfl fun j hj => ?_
      have hr' := (List.nodup_cons.1 hr)
      have he : ((i :: is).toFinset).erase i = is.toFinset := by
        rw [List.toFinset_cons, erase_insert (by simpa using hr'.1)]
      have hce : cols.toFinset.erase j = (cols.erase j).toFinset := by
        ext x
        simp [hc.mem_erase_iff]
      rw [he, hce, ih _ hr'.2 (hc.erase j)]

/-- Partial permanents commute with an injective relabeling of both index sets. -/
theorem permOn_image {A B R : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [CommSemiring R]
    (f : A → B) (hf : Function.Injective f) (M : Matrix B B R) (S T : Finset A) :
    permOn M (S.image f) (T.image f) =
      permOn (Matrix.of fun i j => M (f i) (f j)) S T := by
  classical
  have h := permOn_eq_permOnList M (S.toList.map f) (T.toList.map f)
    (S.nodup_toList.map hf) (T.nodup_toList.map hf)
  have h' := permOn_eq_permOnList (Matrix.of fun i j => M (f i) (f j)) S.toList T.toList
    S.nodup_toList T.nodup_toList
  have hs : (S.toList.map f).toFinset = S.image f := by ext x; simp
  have ht : (T.toList.map f).toFinset = T.image f := by ext x; simp
  rw [hs,ht] at h
  simp only [Finset.toList_toFinset] at h'
  rw [h,h']
  exact permOnList_map f hf (fun i j => M i j) S.toList T.toList

/-- For a matrix with entries `0` and `1`, `permOn` counts the bijections along `1`-entries. -/
theorem permOn_eq_card {M : Matrix V V ℤ} (hM : ∀ i j, M i j = 0 ∨ M i j = 1) (S T : Finset V) :
    permOn M S T = ((bijOn S T).filter fun f => ∀ i ∈ S, M i (f i) = 1).card := by
  classical
  rw [permOn, card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_congr rfl fun f _ => ?_
  split_ifs with h
  · simp [prod_eq_one h]
  · obtain ⟨i, hi, hne⟩ := not_forall₂.1 h
    exact prod_eq_zero hi ((hM i (f i)).resolve_right hne)

end Matrix


-- BEGIN Solutions.PermanentGadget

/- The constant block in Orzel, Srinivasan, Tavenas and Yehudayoff,
   The Algebraic Cost of a Boolean Sum, Section 3.2. -/
namespace PermanentGadget

def block : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1, 1; 1, 0, -1; -(1/2), 1/2, 3/2]

theorem block_minors :
    Matrix.permOnList block [0,1,2] [0,1,2] = 2 ∧
    Matrix.permOnList block [0,1] [0,2] = 0 ∧
    Matrix.permOnList block [0,2] [0,1] = 0 ∧
    Matrix.permOnList block [0,1] [0,1] = 1 ∧
    Matrix.permOnList block [0,2] [0,2] = 1 ∧
    Matrix.permOnList block [0] [0] = 1 := by
  simp (config := { decide := true }) [block,Matrix.permOnList,List.erase]
    <;> norm_num

theorem block_permanent : block.permanent = 2 := by
  rw [Matrix.permanent_eq_permOn]
  have h := Matrix.permOn_eq_permOnList block [0,1,2] [0,1,2] (by decide) (by decide)
  have hu : ([0,1,2] : List (Fin 3)).toFinset = Finset.univ := by decide
  rw [hu] at h
  exact h.trans block_minors.1

theorem block_minor_sets :
    Matrix.permOn block {0,1} {0,2} = 0 ∧
    Matrix.permOn block {0,2} {0,1} = 0 ∧
    Matrix.permOn block {0,1} {0,1} = 1 ∧
    Matrix.permOn block {0,2} {0,2} = 1 ∧
    Matrix.permOn block {0} {0} = 1 := by
  have h01_02 := Matrix.permOn_eq_permOnList block [0,1] [0,2] (by decide) (by decide)
  have h02_01 := Matrix.permOn_eq_permOnList block [0,2] [0,1] (by decide) (by decide)
  have h01_01 := Matrix.permOn_eq_permOnList block [0,1] [0,1] (by decide) (by decide)
  have h02_02 := Matrix.permOn_eq_permOnList block [0,2] [0,2] (by decide) (by decide)
  have h0 := Matrix.permOn_eq_permOnList block [0] [0] (by decide) (by decide)
  simp only [List.toFinset_cons,List.toFinset_nil] at *
  exact ⟨h01_02.trans block_minors.2.1,h02_01.trans block_minors.2.2.1,
    h01_01.trans block_minors.2.2.2.1,h02_02.trans block_minors.2.2.2.2.1,
    h0.trans block_minors.2.2.2.2.2⟩

/-- Partial permanents commute with a change of coefficients. -/
theorem permOn_map {V R S : Type} [Fintype V] [DecidableEq V]
    [CommSemiring R] [CommSemiring S] (f : R →+* S) (M : Matrix V V R)
    (rows cols : Finset V) :
    Matrix.permOn (M.map f) rows cols = f (Matrix.permOn M rows cols) := by
  simp only [Matrix.permOn,map_sum,map_prod,Matrix.map_apply]

noncomputable def complexBlock : Matrix (Fin 3) (Fin 3) ℂ := block.map (Rat.castHom ℂ)

/-- The gadget coefficients used by the mission's complex polynomial ring. -/
theorem complex_block_minors :
    complexBlock.permanent = 2 ∧
    Matrix.permOn complexBlock {0,1} {0,2} = 0 ∧
    Matrix.permOn complexBlock {0,2} {0,1} = 0 ∧
    Matrix.permOn complexBlock {0,1} {0,1} = 1 ∧
    Matrix.permOn complexBlock {0,2} {0,2} = 1 ∧
    Matrix.permOn complexBlock {0} {0} = 1 := by
  have hp : complexBlock.permanent = 2 := by
    rw [complexBlock,← RingHom.map_permanent,block_permanent]
    norm_num
  refine ⟨hp,?_,?_,?_,?_,?_⟩
  all_goals
    simp only [complexBlock,permOn_map,block_minor_sets.1,block_minor_sets.2.1,
      block_minor_sets.2.2.1,block_minor_sets.2.2.2.1,block_minor_sets.2.2.2.2,
      map_zero,map_one]

end PermanentGadget


-- BEGIN Solutions.PermanentProjection
/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/



/- Adapted from cslib-frontier e78796a1e0c0fe124f9130a84850a5104bbe5f14,
CslibFrontier/Computability/Circuit/Arithmetic/Permanent/Projection.lean.
Uses the mission's exact complex projection definition and pair-indexed matrix variables. -/

namespace PermanentFoundation
open MvPolynomial Finset ResultantVNP
variable {n m : ℕ} {σ : Type}

noncomputable def genericMatrix (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => X (i,j)

noncomputable def projection {τ : Type} (ρ : τ → σ ⊕ ℂ) :
    MvPolynomial τ ℂ →ₐ[ℂ] MvPolynomial σ ℂ := aeval (fun v => Sum.elim X C (ρ v))

lemma aeval_permanent_genericMatrix {A : Type} [CommSemiring A] [Algebra ℂ A]
    (x : Fin n × Fin n → A) :
    aeval x (genericMatrix n).permanent = (Matrix.of fun i j : Fin n => x (i,j)).permanent := by
  rw [AlgHom.map_permanent]
  congr 1
  ext i j
  simp [genericMatrix]

lemma projection_permanent_genericMatrix (ρ : Fin m × Fin m → σ ⊕ ℂ) :
    projection ρ (genericMatrix m).permanent =
      (Matrix.of fun i j : Fin m => Sum.elim X (fun a => C a) (ρ (i,j))).permanent :=
  aeval_permanent_genericMatrix _

/-- A polynomial in `MvPolynomial σ ℂ` is a projection substitution entry if it is either a
variable `X i` or a constant `C c`. -/
def IsSubstEntry (p : MvPolynomial σ ℂ) : Prop :=
  ∃ s : σ ⊕ ℂ, Sum.elim X (fun a => C a) s = p

namespace IsSubstEntry

theorem C (c : ℂ) : IsSubstEntry (MvPolynomial.C c : MvPolynomial σ ℂ) :=
  ⟨Sum.inr c, rfl⟩

theorem X (i : σ) : IsSubstEntry (MvPolynomial.X i : MvPolynomial σ ℂ) :=
  ⟨Sum.inl i, rfl⟩

theorem zero : IsSubstEntry (0 : MvPolynomial σ ℂ) :=
  ⟨Sum.inr 0, map_zero _⟩

theorem one : IsSubstEntry (1 : MvPolynomial σ ℂ) :=
  ⟨Sum.inr 1, map_one _⟩

end IsSubstEntry

/-- A matrix over `MvPolynomial σ ℂ` is a specialization of a generic matrix if every entry is a
variable `X i` or a constant `C c`. -/
def IsSubstMatrix {α β : Type*} (M : Matrix α β (MvPolynomial σ ℂ)) : Prop :=
  ∀ i j, IsSubstEntry (M i j)

namespace IsSubstMatrix

theorem zero {α β : Type*} : IsSubstMatrix (0 : Matrix α β (MvPolynomial σ ℂ)) :=
  fun _ _ => .zero

theorem one {α : Type*} [DecidableEq α] :
    IsSubstMatrix (1 : Matrix α α (MvPolynomial σ ℂ)) :=
  fun i j => by
    rw [Matrix.one_apply]
    split_ifs <;> [exact .one; exact .zero]

theorem fromBlocks {α₁ α₂ β₁ β₂ : Type*}
    {A : Matrix α₁ β₁ (MvPolynomial σ ℂ)} {B : Matrix α₁ β₂ (MvPolynomial σ ℂ)}
    {C : Matrix α₂ β₁ (MvPolynomial σ ℂ)} {D : Matrix α₂ β₂ (MvPolynomial σ ℂ)}
    (hA : IsSubstMatrix A) (hB : IsSubstMatrix B) (hC : IsSubstMatrix C) (hD : IsSubstMatrix D) :
    IsSubstMatrix (Matrix.fromBlocks A B C D) := by
  rintro (i | i) (j | j)
  · exact hA i j
  · exact hB i j
  · exact hC i j
  · exact hD i j

theorem submatrix {α β α' β' : Type*} {M : Matrix α β (MvPolynomial σ ℂ)}
    (hM : IsSubstMatrix M) (f : α' → α) (g : β' → β) :
    IsSubstMatrix (M.submatrix f g) :=
  fun i j => hM (f i) (g j)

theorem toBlocks₁₁ {α₁ α₂ β₁ β₂ : Type*} {M : Matrix (α₁ ⊕ α₂) (β₁ ⊕ β₂) (MvPolynomial σ ℂ)}
    (hM : IsSubstMatrix M) : IsSubstMatrix M.toBlocks₁₁ :=
  fun i j => hM (.inl i) (.inl j)

theorem toBlocks₁₂ {α₁ α₂ β₁ β₂ : Type*} {M : Matrix (α₁ ⊕ α₂) (β₁ ⊕ β₂) (MvPolynomial σ ℂ)}
    (hM : IsSubstMatrix M) : IsSubstMatrix M.toBlocks₁₂ :=
  fun i j => hM (.inl i) (.inr j)

theorem toBlocks₂₁ {α₁ α₂ β₁ β₂ : Type*} {M : Matrix (α₁ ⊕ α₂) (β₁ ⊕ β₂) (MvPolynomial σ ℂ)}
    (hM : IsSubstMatrix M) : IsSubstMatrix M.toBlocks₂₁ :=
  fun i j => hM (.inr i) (.inl j)

theorem toBlocks₂₂ {α₁ α₂ β₁ β₂ : Type*} {M : Matrix (α₁ ⊕ α₂) (β₁ ⊕ β₂) (MvPolynomial σ ℂ)}
    (hM : IsSubstMatrix M) : IsSubstMatrix M.toBlocks₂₂ :=
  fun i j => hM (.inr i) (.inr j)

/-- The permanent of any specialization matrix indexed by `α ≃ Fin m` is a projection of
`(genericMatrix m).permanent`. -/
theorem isProjection_permanent {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matrix α α (MvPolynomial σ ℂ)} (hM : IsSubstMatrix M) {m : ℕ} (e : Fin m ≃ α) :
    IsProjection M.permanent (genericMatrix m).permanent := by
  choose ρ hρ using hM
  refine ⟨fun idx =>
    let pq := idx
    ρ (e pq.1) (e pq.2), ?_⟩
  rw [aeval_permanent_genericMatrix, ← M.permanent_submatrix_equiv e]
  exact congrArg Matrix.permanent (Matrix.ext fun i j => by simpa using hρ (e i) (e j))

end IsSubstMatrix

/-- A polynomial `P` is a projection of `(genericMatrix m).permanent` if and only if it is the
permanent of an `m × m` specialization matrix. -/
theorem isProjection_permanent_iff_exists_substMatrix {P : MvPolynomial σ ℂ} {m : ℕ} :
    IsProjection P (genericMatrix m).permanent ↔
      ∃ M : Matrix (Fin m) (Fin m) (MvPolynomial σ ℂ), IsSubstMatrix M ∧ M.permanent = P := by
  constructor
  · rintro ⟨ρ, rfl⟩
    refine ⟨Matrix.of fun i j => Sum.elim X (fun a => C a) (ρ ((i, j))),
      fun i j => ⟨ρ ((i, j)), rfl⟩,
      (projection_permanent_genericMatrix ρ).symm⟩
  · rintro ⟨M, hM, rfl⟩
    exact hM.isProjection_permanent (Equiv.refl _)

/-- The constant polynomial `1` is a projection of the `m × m` generic permanent for every `m`. -/
theorem isProjection_permanent_one (m : ℕ) :
    IsProjection (1 : MvPolynomial σ ℂ) (genericMatrix m).permanent :=
  isProjection_permanent_iff_exists_substMatrix.mpr ⟨1, .one, Matrix.permanent_one⟩

/-- **Multiplicative closure of permanent projections**: if `P` is a projection of the `m × m`
generic permanent and `Q` is a projection of the `k × k` generic permanent, then `P * Q` is a
projection of the `(m + k) × (m + k)` generic permanent. -/
theorem _root_.ResultantVNP.IsProjection.permanent_mul {P Q : MvPolynomial σ ℂ} {m k : ℕ}
    (hP : IsProjection P (genericMatrix m).permanent)
    (hQ : IsProjection Q (genericMatrix k).permanent) :
    IsProjection (P * Q) (genericMatrix (m + k)).permanent := by
  obtain ⟨M₁, hM₁, rfl⟩ := isProjection_permanent_iff_exists_substMatrix.mp hP
  obtain ⟨M₂, hM₂, rfl⟩ := isProjection_permanent_iff_exists_substMatrix.mp hQ
  rw [← Matrix.permanent_fromBlocks_zero M₁ M₂]
  exact (hM₁.fromBlocks .zero .zero hM₂).isProjection_permanent finSumFinEquiv.symm

/-- **Monotonicity of permanent projections in the matrix dimension**: if `m ≤ k` and `P` is a
projection of `(genericMatrix m).permanent`, then `P` is a projection of
`(genericMatrix k).permanent`. -/
theorem isProjection_permanent_mono {P : MvPolynomial σ ℂ} {m k : ℕ} (hmk : m ≤ k)
    (hP : IsProjection P (genericMatrix m).permanent) :
    IsProjection P (genericMatrix k).permanent := by
  have hmul := hP.permanent_mul (isProjection_permanent_one (σ := σ) (k - m))
  rwa [mul_one, Nat.add_sub_of_le hmk] at hmul

end PermanentFoundation


-- BEGIN Solutions.PermanentGadgetMatrix

/- Construction from Orzel, Srinivasan, Tavenas and Yehudayoff,
   The Algebraic Cost of a Boolean Sum, Section 3.2. -/
namespace PermanentGadgetMatrix
open MvPolynomial PermanentFoundation ResultantVNP

variable {σ : Type} {n : ℕ}

noncomputable def gadget (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (a b : Fin n) :
    Matrix (Fin 3 ⊕ Fin n) (Fin 3 ⊕ Fin n) (MvPolynomial σ ℂ) :=
  Matrix.fromBlocks
    (Matrix.of fun i j => C (PermanentGadget.complexBlock i j))
    (Matrix.of fun i j => if (i = 1 ∧ j = a) ∨ (i = 2 ∧ j = b) then 1 else 0)
    (Matrix.of fun i j => if (i = a ∧ j = 1) ∨ (i = b ∧ j = 2) then 1 else 0)
    (Matrix.of fun i j => if (i = a ∧ j = a) ∨ (i = b ∧ j = b) then 0 else M i j)

theorem gadget_entries {M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)}
    (hM : IsSubstMatrix M) (a b : Fin n) : IsSubstMatrix (gadget M a b) := by
  apply IsSubstMatrix.fromBlocks
  · intro i j
    exact IsSubstEntry.C _
  · intro i j
    dsimp
    split_ifs <;> first | exact IsSubstEntry.one | exact IsSubstEntry.zero
  · intro i j
    dsimp
    split_ifs <;> first | exact IsSubstEntry.one | exact IsSubstEntry.zero
  · intro i j
    dsimp
    split_ifs <;> first | exact IsSubstEntry.zero | exact hM i j

/-- The gadget itself is a projection of a permanent of dimension n+3. -/
theorem gadget_isProjection {M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)}
    (hM : IsSubstMatrix M) (a b : Fin n) :
    IsProjection (gadget M a b).permanent (genericMatrix (3+n)).permanent :=
  (gadget_entries hM a b).isProjection_permanent finSumFinEquiv.symm

def gadgetRows : Finset (Fin 3 ⊕ Fin n) := Finset.univ.image Sum.inl

noncomputable def clearedMatrix (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (a b : Fin n) :=
  Matrix.of fun i j => if (i = a ∧ j = a) ∨ (i = b ∧ j = b) then 0 else M i j

lemma otherRows : (Finset.univ : Finset (Fin 3 ⊕ Fin n)) \ gadgetRows =
    Finset.univ.image Sum.inr := by
  ext x
  cases x <;> simp [gadgetRows]

/-- When the three new rows use the three new columns, the other minor is the
    permanent of the original matrix with the two selected entries cleared. -/
theorem bottom_minor_012 (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (a b : Fin n) :
    Matrix.permOn (gadget M a b) (Finset.univ \ gadgetRows)
      (Finset.univ \ ({Sum.inl 0,Sum.inl 1,Sum.inl 2} : Finset (Fin 3 ⊕ Fin n))) =
      (clearedMatrix M a b).permanent := by
  have ht : ({Sum.inl 0,Sum.inl 1,Sum.inl 2} : Finset (Fin 3 ⊕ Fin n)) = gadgetRows := by
    ext x
    cases x with
    | inl i => fin_cases i <;> simp [gadgetRows]
    | inr i => simp [gadgetRows]
  rw [ht,otherRows,Matrix.permOn_image Sum.inr Sum.inr_injective]
  rw [← Matrix.permanent_eq_permOn]
  congr 1

/-- Selecting the second old column forces the second selected old row to
    cover the third new column. -/
theorem bottom_minor_014 (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (hab : a ≠ b) :
    Matrix.permOn (gadget M a b) (Finset.univ \ gadgetRows)
      (Finset.univ \ ({Sum.inl 0,Sum.inl 1,Sum.inr b} : Finset (Fin 3 ⊕ Fin n))) =
    Matrix.permOn (clearedMatrix M a b) (Finset.univ.erase b) (Finset.univ.erase b) := by
  let S : Finset (Fin 3 ⊕ Fin n) := Finset.univ \ gadgetRows
  let T : Finset (Fin 3 ⊕ Fin n) := Finset.univ \ {Sum.inl 0,Sum.inl 1,Sum.inr b}
  have hi : Sum.inr b ∈ S := by simp [S,gadgetRows]
  have hj : Sum.inl 2 ∈ T := by simp [T]
  have hz : ∀ k ∈ S, k ≠ Sum.inr b → gadget M a b k (Sum.inl 2) = 0 := by
    intro k hk hkb
    cases k with
    | inl k => simp [S,gadgetRows] at hk
    | inr k =>
      have hne : k ≠ b := by simpa using hkb
      simp [gadget,hne]
  have hh := Matrix.permOn_forced_column (gadget M a b) hi hj hz
  have hs : S.erase (Sum.inr b) = (Finset.univ.erase b).image Sum.inr := by
    ext x
    cases x <;> simp [S,gadgetRows]
  have ht : T.erase (Sum.inl 2) = (Finset.univ.erase b).image Sum.inr := by
    ext x
    cases x with
    | inl i => fin_cases i <;> simp [T]
    | inr i => simp [T]
  rw [hs,ht,Matrix.permOn_image Sum.inr Sum.inr_injective] at hh
  have hm : (Matrix.of fun i j => gadget M a b (Sum.inr i) (Sum.inr j)) = clearedMatrix M a b := rfl
  rw [hm] at hh
  simpa [S,T,gadget,hab,Ne.symm hab] using hh

theorem bottom_minor_023 (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (hab : a ≠ b) :
    Matrix.permOn (gadget M a b) (Finset.univ \ gadgetRows)
      (Finset.univ \ ({Sum.inl 0,Sum.inl 2,Sum.inr a} : Finset (Fin 3 ⊕ Fin n))) =
    Matrix.permOn (clearedMatrix M a b) (Finset.univ.erase a) (Finset.univ.erase a) := by
  let S : Finset (Fin 3 ⊕ Fin n) := Finset.univ \ gadgetRows
  let T : Finset (Fin 3 ⊕ Fin n) := Finset.univ \ {Sum.inl 0,Sum.inl 2,Sum.inr a}
  have hi : Sum.inr a ∈ S := by simp [S,gadgetRows]
  have hj : Sum.inl 1 ∈ T := by simp [T]
  have hz : ∀ k ∈ S, k ≠ Sum.inr a → gadget M a b k (Sum.inl 1) = 0 := by
    intro k hk hkb
    cases k with
    | inl k => simp [S,gadgetRows] at hk
    | inr k =>
      have hne : k ≠ a := by simpa using hkb
      simp [gadget,hne]
  have hh := Matrix.permOn_forced_column (gadget M a b) hi hj hz
  have hs : S.erase (Sum.inr a) = (Finset.univ.erase a).image Sum.inr := by
    ext x
    cases x <;> simp [S,gadgetRows]
  have ht : T.erase (Sum.inl 1) = (Finset.univ.erase a).image Sum.inr := by
    ext x
    cases x with
    | inl i => fin_cases i <;> simp [T]
    | inr i => simp [T]
  rw [hs,ht,Matrix.permOn_image Sum.inr Sum.inr_injective] at hh
  have hm : (Matrix.of fun i j => gadget M a b (Sum.inr i) (Sum.inr j)) = clearedMatrix M a b := rfl
  rw [hm] at hh
  simpa [S,T,gadget,hab,Ne.symm hab] using hh

/-- Selecting both old columns forces both corresponding old rows. -/
theorem bottom_minor_034 (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (hab : a ≠ b) :
    Matrix.permOn (gadget M a b) (Finset.univ \ gadgetRows)
      (Finset.univ \ ({Sum.inl 0,Sum.inr a,Sum.inr b} : Finset (Fin 3 ⊕ Fin n))) =
    Matrix.permOn (clearedMatrix M a b) ((Finset.univ.erase a).erase b)
      ((Finset.univ.erase a).erase b) := by
  let S : Finset (Fin 3 ⊕ Fin n) := Finset.univ \ gadgetRows
  let T : Finset (Fin 3 ⊕ Fin n) := Finset.univ \ {Sum.inl 0,Sum.inr a,Sum.inr b}
  have hia : Sum.inr a ∈ S := by simp [S,gadgetRows]
  have hja : Sum.inl 1 ∈ T := by simp [T]
  have hza : ∀ k ∈ S, k ≠ Sum.inr a → gadget M a b k (Sum.inl 1) = 0 := by
    intro k hk hka
    cases k with
    | inl k => simp [S,gadgetRows] at hk
    | inr k =>
      have hne : k ≠ a := by simpa using hka
      simp [gadget,hne]
  have hfirst := Matrix.permOn_forced_column (gadget M a b) hia hja hza
  have hib : Sum.inr b ∈ S.erase (Sum.inr a) := by simp [S,gadgetRows,hab,Ne.symm hab]
  have hjb : Sum.inl 2 ∈ T.erase (Sum.inl 1) := by simp [T]
  have hzb : ∀ k ∈ S.erase (Sum.inr a), k ≠ Sum.inr b → gadget M a b k (Sum.inl 2) = 0 := by
    intro k hk hkb
    cases k with
    | inl k => simp [S,gadgetRows] at hk
    | inr k =>
      have hne : k ≠ b := by simpa using hkb
      simp [gadget,hne]
  have hsecond := Matrix.permOn_forced_column (gadget M a b) hib hjb hzb
  have hs : (S.erase (Sum.inr a)).erase (Sum.inr b) =
      ((Finset.univ.erase a).erase b).image Sum.inr := by
    ext x
    cases x <;> simp [S,gadgetRows]
  have ht : (T.erase (Sum.inl 1)).erase (Sum.inl 2) =
      ((Finset.univ.erase a).erase b).image Sum.inr := by
    ext x
    cases x with
    | inl i => fin_cases i <;> simp [T]
    | inr i => simp [T,Finset.mem_erase, and_left_comm, and_comm, and_assoc]
  rw [hs,ht,Matrix.permOn_image Sum.inr Sum.inr_injective] at hsecond
  have hm : (Matrix.of fun i j => gadget M a b (Sum.inr i) (Sum.inr j)) = clearedMatrix M a b := rfl
  rw [hm] at hsecond
  rw [hsecond] at hfirst
  simpa [S,T,gadget,hab,Ne.symm hab] using hfirst

lemma gadgetRows_card : (gadgetRows (n := n)).card = 3 := by
  simp [gadgetRows,Finset.card_image_of_injective,Sum.inl_injective]
def activeColumns (a b : Fin n) : Finset (Fin 3 ⊕ Fin n) :=
  gadgetRows ∪ {Sum.inr a,Sum.inr b}

def contributingColumns (a b : Fin n) : Finset (Finset (Fin 3 ⊕ Fin n)) :=
  {{Sum.inl 0,Sum.inl 1,Sum.inl 2}, {Sum.inl 0,Sum.inl 1,Sum.inr b},
    {Sum.inl 0,Sum.inl 2,Sum.inr a}, {Sum.inl 0,Sum.inr a,Sum.inr b}}

lemma contributingColumns_subset (a b : Fin n) (hab : a ≠ b) :
    contributingColumns a b ⊆ (activeColumns a b).powerset.filter
      (fun cols => cols.card = 3 ∧ Sum.inl 0 ∈ cols ∧
        cols ≠ {Sum.inl 0,Sum.inl 1,Sum.inr a} ∧
        cols ≠ {Sum.inl 0,Sum.inl 2,Sum.inr b}) := by
  intro cols hc
  simp only [contributingColumns,Finset.mem_insert,Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) [activeColumns,gadgetRows,Finset.subset_iff,hab,Ne.symm hab,
      Finset.ext_iff]
  · exact ⟨a,by simp [hab,Ne.symm hab]⟩
  · exact ⟨a,by simp [hab,Ne.symm hab]⟩

lemma contributingColumns_card (a b : Fin n) (hab : a ≠ b) :
    (contributingColumns a b).card = 4 := by
  simp (config := { decide := true }) [contributingColumns,Finset.ext_iff,hab,Ne.symm hab]
  all_goals exact ⟨a,by simp [hab,Ne.symm hab]⟩

/-- A fixed five-element indexing of the active columns. -/
def activeIndex (a b : Fin n) (i : Fin 5) : Fin 3 ⊕ Fin n :=
  if h : i.val < 3 then Sum.inl ⟨i.val,h⟩ else if i.val = 3 then Sum.inr a else Sum.inr b

lemma activeIndex_injective (a b : Fin n) (hab : a ≠ b) :
    Function.Injective (activeIndex a b) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [activeIndex]

lemma activeColumns_card (a b : Fin n) (hab : a ≠ b) : (activeColumns a b).card = 5 := by
  have hd : Disjoint (gadgetRows (n := n)) ({Sum.inr a,Sum.inr b} : Finset (Fin 3 ⊕ Fin n)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    simp at hy
  rw [activeColumns,Finset.card_union_of_disjoint hd,gadgetRows_card]
  simp [hab]

lemma active_triples_card (a b : Fin n) (hab : a ≠ b) :
    ((activeColumns a b).powerset.filter (fun cols => cols.card = 3)).card = 10 := by
  rw [← Finset.powersetCard_eq_filter,Finset.card_powersetCard,activeColumns_card a b hab]
  decide

lemma anchored_triples_card (a b : Fin n) (hab : a ≠ b) :
    ((activeColumns a b).powerset.filter
      (fun cols => cols.card = 3 ∧ Sum.inl 0 ∈ cols)).card = 6 := by
  have hs : ({Sum.inl 0} : Finset (Fin 3 ⊕ Fin n)) ⊆ activeColumns a b := by
    simp [activeColumns,gadgetRows]
  have hh := Finset.card_filter_powersetCard_subset
    ({Sum.inl 0} : Finset (Fin 3 ⊕ Fin n)) (activeColumns a b) 3 hs (by simp)
  rw [activeColumns_card a b hab] at hh
  norm_num at hh
  convert hh using 1
  · congr 1
    ext cols
    simp [Finset.mem_powersetCard,Finset.subset_iff,and_assoc]
  · decide

lemma contributingColumns_eq (a b : Fin n) (hab : a ≠ b) :
    contributingColumns a b = (activeColumns a b).powerset.filter
      (fun cols => cols.card = 3 ∧ Sum.inl 0 ∈ cols ∧
        cols ≠ {Sum.inl 0,Sum.inl 1,Sum.inr a} ∧
        cols ≠ {Sum.inl 0,Sum.inl 2,Sum.inr b}) := by
  let anchor := (activeColumns a b).powerset.filter (fun cols => cols.card = 3 ∧ Sum.inl 0 ∈ cols)
  let x : Finset (Fin 3 ⊕ Fin n) := {Sum.inl 0,Sum.inl 1,Sum.inr a}
  let y : Finset (Fin 3 ⊕ Fin n) := {Sum.inl 0,Sum.inl 2,Sum.inr b}
  have hx : x ∈ anchor := by simp [anchor,x,activeColumns,gadgetRows,Finset.subset_iff]
  have hy : y ∈ anchor := by simp [anchor,y,activeColumns,gadgetRows,Finset.subset_iff]
  have hxy : x ≠ y := by
    intro he
    have hh : Sum.inl 1 ∈ x := by simp [x]
    rw [he] at hh
    simp [y] at hh
  have hy' : y ∈ anchor.erase x := by simp [hy,hxy.symm]
  have hc : (anchor.erase x |>.erase y).card = 4 := by
    rw [Finset.card_erase_of_mem hy',Finset.card_erase_of_mem hx]
    change (anchor.card - 1) - 1 = 4
    rw [show anchor.card = 6 from anchored_triples_card a b hab]
  have he : (activeColumns a b).powerset.filter
      (fun cols => cols.card = 3 ∧ Sum.inl 0 ∈ cols ∧ cols ≠ x ∧ cols ≠ y) =
      (anchor.erase x).erase y := by
    ext cols
    simp [anchor,Finset.mem_filter,Finset.mem_erase,and_assoc,and_left_comm,and_comm]
  have hs := contributingColumns_subset a b hab
  change contributingColumns a b ⊆ (activeColumns a b).powerset.filter
    (fun cols => cols.card = 3 ∧ Sum.inl 0 ∈ cols ∧ cols ≠ x ∧ cols ≠ y) at hs
  apply Finset.eq_of_subset_of_card_le hs
  rw [he,hc,contributingColumns_card a b hab]

lemma outside_active_zero (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (i j : Fin 3 ⊕ Fin n) (hi : i ∈ gadgetRows) (hj : j ∉ activeColumns a b) :
    gadget M a b i j = 0 := by
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hi
  cases j with
  | inl j =>
    exfalso
    apply hj
    simp [activeColumns,gadgetRows]
  | inr j =>
    have hja : j ≠ a := by intro h; subst j; apply hj; simp [activeColumns]
    have hjb : j ≠ b := by intro h; subst j; apply hj; simp [activeColumns]
    simp [gadget,hja,hjb]

/-- A column outside the five active columns makes a top-row minor vanish. -/
lemma top_minor_zero (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (cols : Finset (Fin 3 ⊕ Fin n)) (h : ¬cols ⊆ activeColumns a b) :
    Matrix.permOn (gadget M a b) gadgetRows cols = 0 := by
  obtain ⟨j,hj,houtside⟩ := Finset.not_subset.mp h
  exact Matrix.permOn_eq_zero_of_col hj (fun i hi => outside_active_zero M a b i j hi houtside)

/-- The old rows have zero entries in the first new column. -/
lemma old_row_first_column_zero (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (i : Fin 3 ⊕ Fin n) (hi : i ∈ Finset.univ \ gadgetRows) :
    gadget M a b i (Sum.inl 0) = 0 := by
  have hn : i ∉ gadgetRows := (Finset.mem_sdiff.mp hi).2
  cases i with
  | inl i => exfalso; apply hn; simp [gadgetRows]
  | inr i => simp [gadget]

/-- The first new column must be used by a new row in every nonzero expansion term. -/
lemma bottom_minor_zero (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (cols : Finset (Fin 3 ⊕ Fin n)) (h : Sum.inl 0 ∉ cols) :
    Matrix.permOn (gadget M a b) (Finset.univ \ gadgetRows) (Finset.univ \ cols) = 0 := by
  apply Matrix.permOn_eq_zero_of_col (j := Sum.inl 0)
  · simp [h]
  · intro i hi
    exact old_row_first_column_zero M a b i hi

/-- Explicit list expansion for a top-row minor, used for the finite gadget calculation. -/
lemma top_minor_as_list (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (cols : List (Fin 3 ⊕ Fin n)) (hc : cols.Nodup) :
    Matrix.permOn (gadget M a b) gadgetRows cols.toFinset =
      Matrix.permOnList (gadget M a b) [Sum.inl 0,Sum.inl 1,Sum.inl 2] cols := by
  have h := Matrix.permOn_eq_permOnList (gadget M a b)
    [Sum.inl 0,Sum.inl 1,Sum.inl 2] cols (by simp) hc
  have hr : ([Sum.inl 0,Sum.inl 1,Sum.inl 2] : List (Fin 3 ⊕ Fin n)).toFinset = gadgetRows := by
    ext x
    cases x with
    | inl i => fin_cases i <;> simp [gadgetRows]
    | inr i => simp [gadgetRows]
  simpa only [hr] using h

lemma top_minor_013 (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (hab : a ≠ b) : Matrix.permOn (gadget M a b) gadgetRows
      {Sum.inl 0,Sum.inl 1,Sum.inr a} = 0 := by
  have hh := top_minor_as_list M a b [Sum.inl 0,Sum.inl 1,Sum.inr a] (by simp)
  simp at hh
  rw [hh]
  have he := Matrix.permOnList_map (activeIndex a b) (activeIndex_injective a b hab)
    (gadget M a b) [0,1,2] [0,1,3]
  norm_num [activeIndex] at he
  have he' : Matrix.permOnList (gadget M a b) [Sum.inl 0,Sum.inl 1,Sum.inl 2]
      [Sum.inl 0,Sum.inl 1,Sum.inr a] =
      Matrix.permOnList (fun i j => gadget M a b (activeIndex a b i) (activeIndex a b j))
        [0,1,2] [0,1,3] := by
    convert he using 1 <;> first | rfl | simp
  rw [he']
  simp (config := { decide := true }) [Matrix.permOnList,List.erase,activeIndex,gadget,
    PermanentGadget.complexBlock,PermanentGadget.block,hab] <;> norm_num

lemma top_minor_012 (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (hab : a ≠ b) : Matrix.permOn (gadget M a b) gadgetRows
      {Sum.inl 0,Sum.inl 1,Sum.inl 2} = 2 := by
  have hh := top_minor_as_list M a b [Sum.inl 0,Sum.inl 1,Sum.inl 2] (by simp)
  simp at hh
  rw [hh]
  have he := Matrix.permOnList_map (activeIndex a b) (activeIndex_injective a b hab)
    (gadget M a b) [0,1,2] [0,1,2]
  norm_num [activeIndex] at he
  have he' : Matrix.permOnList (gadget M a b) [Sum.inl 0,Sum.inl 1,Sum.inl 2]
      [Sum.inl 0,Sum.inl 1,Sum.inl 2] =
      Matrix.permOnList (fun i j => gadget M a b (activeIndex a b i) (activeIndex a b j))
        [0,1,2] [0,1,2] := by
    convert he using 1 <;> first | rfl | simp
  rw [he']
  simp (config := { decide := true }) [Matrix.permOnList,List.erase,activeIndex,gadget,
    PermanentGadget.complexBlock,PermanentGadget.block,hab] <;> norm_num
  simpa only [map_add,map_ofNat] using
    congrArg (C : ℂ → MvPolynomial σ ℂ) (by norm_num : (3:ℂ)/2+1/2=2)

lemma top_minor_014 (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (hab : a ≠ b) : Matrix.permOn (gadget M a b) gadgetRows
      {Sum.inl 0,Sum.inl 1,Sum.inr b} = 1 := by
  have hh := top_minor_as_list M a b [Sum.inl 0,Sum.inl 1,Sum.inr b] (by simp)
  simp at hh
  rw [hh]
  have he := Matrix.permOnList_map (activeIndex a b) (activeIndex_injective a b hab)
    (gadget M a b) [0,1,2] [0,1,4]
  norm_num [activeIndex] at he
  have he' : Matrix.permOnList (gadget M a b) [Sum.inl 0,Sum.inl 1,Sum.inl 2]
      [Sum.inl 0,Sum.inl 1,Sum.inr b] =
      Matrix.permOnList (fun i j => gadget M a b (activeIndex a b i) (activeIndex a b j))
        [0,1,2] [0,1,4] := by
    convert he using 1 <;> first | rfl | simp
  rw [he']
  simp (config := { decide := true }) [Matrix.permOnList,List.erase,activeIndex,gadget,
    PermanentGadget.complexBlock,PermanentGadget.block,hab] <;> norm_num

lemma top_minor_023 (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (hab : a ≠ b) : Matrix.permOn (gadget M a b) gadgetRows
      {Sum.inl 0,Sum.inl 2,Sum.inr a} = 1 := by
  have hh := top_minor_as_list M a b [Sum.inl 0,Sum.inl 2,Sum.inr a] (by simp)
  simp at hh
  rw [hh]
  have he := Matrix.permOnList_map (activeIndex a b) (activeIndex_injective a b hab)
    (gadget M a b) [0,1,2] [0,2,3]
  norm_num [activeIndex] at he
  have he' : Matrix.permOnList (gadget M a b) [Sum.inl 0,Sum.inl 1,Sum.inl 2]
      [Sum.inl 0,Sum.inl 2,Sum.inr a] =
      Matrix.permOnList (fun i j => gadget M a b (activeIndex a b i) (activeIndex a b j))
        [0,1,2] [0,2,3] := by
    convert he using 1 <;> first | rfl | simp
  rw [he']
  simp (config := { decide := true }) [Matrix.permOnList,List.erase,activeIndex,gadget,
    PermanentGadget.complexBlock,PermanentGadget.block,hab] <;> norm_num
  simpa only [map_add,map_neg,map_one] using
    congrArg (C : ℂ → MvPolynomial σ ℂ) (by norm_num : (3:ℂ)/2 + -(1/2)=1)

lemma top_minor_024 (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (hab : a ≠ b) : Matrix.permOn (gadget M a b) gadgetRows
      {Sum.inl 0,Sum.inl 2,Sum.inr b} = 0 := by
  have hh := top_minor_as_list M a b [Sum.inl 0,Sum.inl 2,Sum.inr b] (by simp)
  simp at hh
  rw [hh]
  have he := Matrix.permOnList_map (activeIndex a b) (activeIndex_injective a b hab)
    (gadget M a b) [0,1,2] [0,2,4]
  norm_num [activeIndex] at he
  have he' : Matrix.permOnList (gadget M a b) [Sum.inl 0,Sum.inl 1,Sum.inl 2]
      [Sum.inl 0,Sum.inl 2,Sum.inr b] =
      Matrix.permOnList (fun i j => gadget M a b (activeIndex a b i) (activeIndex a b j))
        [0,1,2] [0,2,4] := by
    convert he using 1 <;> first | rfl | simp
  rw [he']
  simp (config := { decide := true }) [Matrix.permOnList,List.erase,activeIndex,gadget,
    PermanentGadget.complexBlock,PermanentGadget.block,hab,Ne.symm hab] <;> norm_num

lemma top_minor_034 (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (hab : a ≠ b) : Matrix.permOn (gadget M a b) gadgetRows
      {Sum.inl 0,Sum.inr a,Sum.inr b} = 1 := by
  have hh := top_minor_as_list M a b [Sum.inl 0,Sum.inr a,Sum.inr b] (by simp [hab])
  simp at hh
  rw [hh]
  have he := Matrix.permOnList_map (activeIndex a b) (activeIndex_injective a b hab)
    (gadget M a b) [0,1,2] [0,3,4]
  norm_num [activeIndex] at he
  have he' : Matrix.permOnList (gadget M a b) [Sum.inl 0,Sum.inl 1,Sum.inl 2]
      [Sum.inl 0,Sum.inr a,Sum.inr b] =
      Matrix.permOnList (fun i j => gadget M a b (activeIndex a b i) (activeIndex a b j))
        [0,1,2] [0,3,4] := by
    convert he using 1 <;> first | rfl | simp
  rw [he']
  simp (config := { decide := true }) [Matrix.permOnList,List.erase,activeIndex,gadget,
    PermanentGadget.complexBlock,PermanentGadget.block,hab,Ne.symm hab] <;> norm_num

/-- Expansion along the three new rows, the starting point for the gadget identity. -/
theorem gadget_expand (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (a b : Fin n) :
    (gadget M a b).permanent =
      ∑ cols ∈ (Finset.univ : Finset (Fin 3 ⊕ Fin n)).powerset,
        Matrix.permOn (gadget M a b) gadgetRows cols *
          Matrix.permOn (gadget M a b) (Finset.univ \ gadgetRows) (Finset.univ \ cols) := by
  rw [Matrix.permanent_eq_permOn,Matrix.permOn_split (gadget M a b) (Finset.subset_univ gadgetRows)]

/-- Only subsets of the three new columns and the two selected old columns contribute. -/
theorem gadget_expand_active (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (a b : Fin n) :
    (gadget M a b).permanent =
      ∑ cols ∈ (activeColumns a b).powerset,
        Matrix.permOn (gadget M a b) gadgetRows cols *
          Matrix.permOn (gadget M a b) (Finset.univ \ gadgetRows) (Finset.univ \ cols) := by
  rw [gadget_expand]
  symm
  apply Finset.sum_subset (Finset.powerset_mono.mpr (Finset.subset_univ _))
  intro cols _ hn
  have hnot : ¬cols ⊆ activeColumns a b := by simpa only [Finset.mem_powerset] using hn
  rw [top_minor_zero M a b cols hnot,zero_mul]

/-- Only three-column subsets can match the gadget's three new rows. -/
theorem gadget_expand_triples (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (a b : Fin n) :
    (gadget M a b).permanent =
      ∑ cols ∈ (activeColumns a b).powerset.filter (fun cols => cols.card = 3),
        Matrix.permOn (gadget M a b) gadgetRows cols *
          Matrix.permOn (gadget M a b) (Finset.univ \ gadgetRows) (Finset.univ \ cols) := by
  rw [gadget_expand_active]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro cols hmem hn
  have hne : cols.card ≠ 3 := by
    intro hc
    apply hn
    exact Finset.mem_filter.mpr ⟨hmem,hc⟩
  rw [Matrix.permOn_eq_zero_of_card_ne _ _ _ (by simpa [gadgetRows_card] using hne.symm),zero_mul]

/-- The expansion reduces to triples containing the first new column. -/
theorem gadget_expand_anchored (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (a b : Fin n) :
    (gadget M a b).permanent =
      ∑ cols ∈ (activeColumns a b).powerset.filter
          (fun cols => cols.card = 3 ∧ Sum.inl 0 ∈ cols),
        Matrix.permOn (gadget M a b) gadgetRows cols *
          Matrix.permOn (gadget M a b) (Finset.univ \ gadgetRows) (Finset.univ \ cols) := by
  rw [gadget_expand_triples]
  symm
  apply Finset.sum_subset (by
    intro cols hc
    simp only [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1,hc.2.1⟩)
  intro cols hmem hn
  have hnot : Sum.inl 0 ∉ cols := by
    intro h
    apply hn
    have hm := Finset.mem_filter.mp hmem
    exact Finset.mem_filter.mpr ⟨hm.1,hm.2,h⟩
  rw [bottom_minor_zero M a b cols hnot,mul_zero]

/-- Remove the two anchored triples whose top minors vanish. -/
theorem gadget_expand_nonzero (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (hab : a ≠ b) :
    (gadget M a b).permanent =
      ∑ cols ∈ (activeColumns a b).powerset.filter
          (fun cols => cols.card = 3 ∧ Sum.inl 0 ∈ cols ∧
            cols ≠ {Sum.inl 0,Sum.inl 1,Sum.inr a} ∧
            cols ≠ {Sum.inl 0,Sum.inl 2,Sum.inr b}),
        Matrix.permOn (gadget M a b) gadgetRows cols *
          Matrix.permOn (gadget M a b) (Finset.univ \ gadgetRows) (Finset.univ \ cols) := by
  rw [gadget_expand_anchored]
  symm
  apply Finset.sum_subset (by
    intro cols hc
    simp only [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1,hc.2.1,hc.2.2.1⟩)
  intro cols hmem hn
  have hm := Finset.mem_filter.mp hmem
  by_cases h1 : cols = {Sum.inl 0,Sum.inl 1,Sum.inr a}
  · rw [h1,top_minor_013 M a b hab,zero_mul]
  · have h2 : cols = {Sum.inl 0,Sum.inl 2,Sum.inr b} := by
      by_contra h2
      apply hn
      exact Finset.mem_filter.mpr ⟨hm.1,hm.2.1,hm.2.2,h1,h2⟩
    rw [h2,top_minor_024 M a b hab,zero_mul]

/-- The permanent is the sum of exactly four lower minors with coefficients 2,1,1,1. -/
theorem gadget_expand_four (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (hab : a ≠ b) :
    (gadget M a b).permanent =
      2 * (clearedMatrix M a b).permanent +
      Matrix.permOn (gadget M a b) (Finset.univ \ gadgetRows)
        (Finset.univ \ {Sum.inl 0,Sum.inl 1,Sum.inr b}) +
      Matrix.permOn (gadget M a b) (Finset.univ \ gadgetRows)
        (Finset.univ \ {Sum.inl 0,Sum.inl 2,Sum.inr a}) +
      Matrix.permOn (gadget M a b) (Finset.univ \ gadgetRows)
        (Finset.univ \ {Sum.inl 0,Sum.inr a,Sum.inr b}) := by
  rw [gadget_expand_nonzero M a b hab,← contributingColumns_eq a b hab]
  simp (config := { decide := true }) [contributingColumns,Finset.ext_iff,
    top_minor_012 M a b hab,top_minor_014 M a b hab,top_minor_023 M a b hab,
    top_minor_034 M a b hab,bottom_minor_012,hab,Ne.symm hab,add_assoc]
  all_goals exact ⟨a,by simp [hab,Ne.symm hab]⟩

/-- The gadget expands into the four relevant minors of the cleared matrix. -/
theorem gadget_cleared_minors (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (hab : a ≠ b) :
    (gadget M a b).permanent =
      2 * (clearedMatrix M a b).permanent +
      Matrix.permOn (clearedMatrix M a b) (Finset.univ.erase b) (Finset.univ.erase b) +
      Matrix.permOn (clearedMatrix M a b) (Finset.univ.erase a) (Finset.univ.erase a) +
      Matrix.permOn (clearedMatrix M a b) ((Finset.univ.erase a).erase b)
        ((Finset.univ.erase a).erase b) := by
  rw [gadget_expand_four M a b hab,bottom_minor_014 M a b hab,
    bottom_minor_023 M a b hab,bottom_minor_034 M a b hab]

/-- Simultaneously restore the two cleared diagonal entries to one. -/
noncomputable def restoredMatrix (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) :=
  let D := clearedMatrix M a b
  let A := D.updateRow a (Function.update (D a) a 1)
  A.updateRow b (Function.update (A b) b 1)

theorem restoredMatrix_minors (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (hab : a ≠ b) :
    (restoredMatrix M a b).permanent = (clearedMatrix M a b).permanent +
      Matrix.permOn (clearedMatrix M a b) (Finset.univ.erase a) (Finset.univ.erase a) +
      Matrix.permOn (clearedMatrix M a b) (Finset.univ.erase b) (Finset.univ.erase b) +
      Matrix.permOn (clearedMatrix M a b) ((Finset.univ.erase a).erase b)
        ((Finset.univ.erase a).erase b) := by
  let D := clearedMatrix M a b
  let A := D.updateRow a (Function.update (D a) a 1)
  have ha : D a a = 0 := by simp [D,clearedMatrix]
  have hb : A b b = 0 := by simp [A,D,clearedMatrix,hab,Ne.symm hab]
  have hA := Matrix.permOn_set_diagonal_one D Finset.univ a (Finset.mem_univ _) ha
  have hB := Matrix.permOn_set_diagonal_one A Finset.univ b (Finset.mem_univ _) hb
  have hmin := Matrix.permOn_set_diagonal_one D (Finset.univ.erase b) a
    (by simp [hab]) ha
  rw [← Matrix.permanent_eq_permOn] at hA hB
  have hA' : A.permanent = D.permanent +
      Matrix.permOn D (Finset.univ.erase a) (Finset.univ.erase a) := by
    simpa only [Matrix.permanent_eq_permOn] using hA
  have hB' : (A.updateRow b (Function.update (A b) b 1)).permanent =
      A.permanent + Matrix.permOn A (Finset.univ.erase b) (Finset.univ.erase b) := by
    simpa only [Matrix.permanent_eq_permOn] using hB
  have herase : (Finset.univ.erase b).erase a = (Finset.univ.erase a).erase b := by
    ext x; simp [and_comm]
  rw [herase] at hmin
  change (restoredMatrix M a b).permanent = _
  change (A.updateRow b (Function.update (A b) b 1)).permanent = _
  rw [hB',hA',hmin]
  simp only [D]
  ac_rfl

/-- The gadget implements the sum of the two simultaneous Boolean substitutions. -/
theorem gadget_boolean_sum (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (a b : Fin n) (hab : a ≠ b) :
    (gadget M a b).permanent = (clearedMatrix M a b).permanent +
      (restoredMatrix M a b).permanent := by
  rw [gadget_cleared_minors M a b hab,restoredMatrix_minors M a b hab]
  ring

/-- A two-occurrence Boolean sum is a permanent projection with three extra
    dimensions when the occurrences lie in distinct rows and columns. -/
theorem boolean_sum_isProjection {M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)}
    (hM : IsSubstMatrix M) (a b : Fin n) (hab : a ≠ b) :
    IsProjection ((clearedMatrix M a b).permanent + (restoredMatrix M a b).permanent)
      (genericMatrix (3+n)).permanent := by
  rw [← gadget_boolean_sum M a b hab]
  exact gadget_isProjection hM a b

end PermanentGadgetMatrix


-- BEGIN Solutions.PermanentGadgetReindex

namespace PermanentGadgetReindex
open MvPolynomial ResultantVNP PermanentFoundation PermanentGadgetMatrix

variable {σ : Type} {n : ℕ}

/-- A permutation can send any two distinct indices to any other two. -/
theorem exists_two_point_permutation {α : Type} [DecidableEq α]
    (a b c d : α) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ e : Equiv.Perm α, e a = c ∧ e b = d := by
  let p := Equiv.swap a c
  have hpc : p b ≠ c := by
    intro h
    apply hab
    apply p.injective
    simpa [p] using h.symm
  let e := p.trans (Equiv.swap (p b) d)
  refine ⟨e,?_,?_⟩
  · simp only [e,Equiv.trans_apply,p,Equiv.swap_apply_left]
    apply Equiv.swap_apply_of_ne_of_ne
    · exact hpc.symm
    · exact hcd
  · simp [e]

noncomputable def setTwo (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (i j k l : Fin n) (z : MvPolynomial σ ℂ) : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ) :=
  Matrix.of fun r c => if (r = i ∧ c = j) ∨ (r = k ∧ c = l) then z else M r c

theorem reindex_cleared (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (i j k l : Fin n) (e : Equiv.Perm (Fin n)) (hei : e i = j) (hek : e k = l) :
    clearedMatrix (M.submatrix id e) i k = (setTwo M i j k l 0).submatrix id e := by
  ext r c
  simp only [clearedMatrix,setTwo,Matrix.of_apply,Matrix.submatrix_apply,id_eq]
  have h1 : e c = j ↔ c = i := by rw [← hei]; exact e.injective.eq_iff
  have h2 : e c = l ↔ c = k := by rw [← hek]; exact e.injective.eq_iff
  simp [h1,h2]

theorem reindex_restored (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (i j k l : Fin n) (hik : i ≠ k) (e : Equiv.Perm (Fin n)) (hei : e i = j) (hek : e k = l) :
    restoredMatrix (M.submatrix id e) i k = (setTwo M i j k l 1).submatrix id e := by
  apply Matrix.ext
  intro r c
  have h1 : e c = j ↔ c = i := by rw [← hei]; exact e.injective.eq_iff
  have h2 : e c = l ↔ c = k := by rw [← hek]; exact e.injective.eq_iff
  by_cases hri : r = i <;> by_cases hrk : r = k <;> by_cases hci : c = i <;> by_cases hck : c = k <;>
    simp_all [restoredMatrix,clearedMatrix,setTwo,Matrix.updateRow,Function.update]

/-- The gadget handles any two entries in distinct rows and columns. -/
theorem boolean_sum_arbitrary_positions
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (i j k l : Fin n) (hik : i ≠ k) (hjl : j ≠ l) :
    IsProjection ((setTwo M i j k l 0).permanent + (setTwo M i j k l 1).permanent)
      (genericMatrix (3+n)).permanent := by
  obtain ⟨e,hei,hek⟩ := exists_two_point_permutation i k j l hik hjl
  have hp := boolean_sum_isProjection (hM.submatrix id e) i k hik
  rw [reindex_cleared M i j k l e hei hek,
    reindex_restored M i j k l hik e hei hek] at hp
  have hperm (N : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) :
      (N.submatrix id e).permanent = N.permanent :=
    Matrix.permanent_submatrix_equiv_equiv (Equiv.refl _) e N
  simpa only [hperm] using hp

end PermanentGadgetReindex


-- BEGIN Solutions.PermanentOccurrence

namespace PermanentOccurrence
open MvPolynomial PermanentGadgetMatrix

variable {σ : Type} [DecidableEq σ]

lemma constant_ne_variable (c : ℂ) (v : σ) :
    (C c : MvPolynomial σ ℂ) ≠ X v := by
  intro h
  have hh := congrArg (pderiv v) h
  simpa using hh

noncomputable def occurrences {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix α α (MvPolynomial σ ℂ)) (v : σ) : Finset (α × α) :=
  Finset.univ.filter fun ij => M ij.1 ij.2 = X v

theorem gadget_occurrences_subset {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (a b : Fin n) (v : σ) :
    occurrences (gadget M a b) v ⊆
      (occurrences M v).image (fun ij => (Sum.inr ij.1,Sum.inr ij.2)) := by
  intro ⟨r,c⟩ h
  have hval : gadget M a b r c = X v := (Finset.mem_filter.mp h).2
  cases r with
  | inl r =>
    cases c with
    | inl c => exact (constant_ne_variable _ v hval).elim
    | inr c =>
      change (if (r = 1 ∧ c = a) ∨ (r = 2 ∧ c = b) then 1 else 0) = X v at hval
      split_ifs at hval
      · exact (constant_ne_variable 1 v (by simpa using hval)).elim
      · exact ((X_ne_zero v) hval.symm).elim
  | inr r =>
    cases c with
    | inl c =>
      change (if (r = a ∧ c = 1) ∨ (r = b ∧ c = 2) then 1 else 0) = X v at hval
      split_ifs at hval
      · exact (constant_ne_variable 1 v (by simpa using hval)).elim
      · exact ((X_ne_zero v) hval.symm).elim
    | inr c =>
      change (if (r = a ∧ c = a) ∨ (r = b ∧ c = b) then 0 else M r c) = X v at hval
      split_ifs at hval with hz
      · exact ((X_ne_zero v) hval.symm).elim
      · apply Finset.mem_image.mpr
        refine ⟨(r,c),?_,rfl⟩
        simp [occurrences,hval]

/-- The gadget never increases the number of occurrences of any variable. -/
theorem gadget_occurrences_card_le {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (a b : Fin n) (v : σ) :
    (occurrences (gadget M a b) v).card ≤ (occurrences M v).card := by
  exact (Finset.card_le_card (gadget_occurrences_subset M a b v)).trans Finset.card_image_le

/-- If a variable occurs only at the two cleared positions, the gadget removes it entirely. -/
theorem gadget_eliminates {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (a b : Fin n) (v : σ)
    (hcover : ∀ i j, M i j = X v → (i = a ∧ j = a) ∨ (i = b ∧ j = b)) :
    occurrences (gadget M a b) v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ⟨r,c⟩ h
  have hv : gadget M a b r c = X v := (Finset.mem_filter.mp h).2
  have him := gadget_occurrences_subset M a b v h
  obtain ⟨⟨i,j⟩,hij,he⟩ := Finset.mem_image.mp him
  have hm : M i j = X v := (Finset.mem_filter.mp hij).2
  have hc := hcover i j hm
  cases he
  change (if (i = a ∧ j = a) ∨ (i = b ∧ j = b) then 0 else M i j) = X v at hv
  rw [if_pos hc] at hv
  exact X_ne_zero v hv.symm

/-- Permuting columns preserves the number of occurrences of every variable. -/
theorem reindex_occurrences_card {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (e : Equiv.Perm (Fin n)) (v : σ) :
    (occurrences (M.submatrix id e) v).card = (occurrences M v).card := by
  apply Finset.card_bij (fun ij _ => (ij.1,e ij.2))
  · intro ij hij
    simpa [occurrences] using (Finset.mem_filter.mp hij).2
  · intro ij hij kl hkl heq
    cases ij with
    | mk i j =>
      cases kl with
      | mk k l =>
        have hk : i = k := (Prod.mk.inj heq).1
        have hl : j = l := e.injective (Prod.mk.inj heq).2
        cases hk; cases hl; rfl
  · intro ij hij
    refine ⟨(ij.1,e.symm ij.2),?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simpa using (Finset.mem_filter.mp hij).2
    · simp

/-- Transposition preserves occurrence counts. -/
theorem transpose_occurrences_card {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (v : σ) :
    (occurrences M.transpose v).card = (occurrences M v).card := by
  apply Finset.card_bij (fun ij _ => (ij.2,ij.1))
  · intro ij hij
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,(Finset.mem_filter.mp hij).2⟩
  · intro ij hij kl hkl heq
    cases ij; cases kl
    simpa only [Prod.mk.injEq] using And.symm (Prod.mk.inj heq)
  · intro ij hij
    refine ⟨(ij.2,ij.1),?_,?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,(Finset.mem_filter.mp hij).2⟩
    · cases ij; rfl

/-- Relabeling both indices through any finite equivalence preserves occurrences. -/
theorem equiv_occurrences_card {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (M : Matrix β β (MvPolynomial σ ℂ)) (e : α ≃ β) (v : σ) :
    (occurrences (M.submatrix e e) v).card = (occurrences M v).card := by
  apply Finset.card_bij (fun ij _ => (e ij.1,e ij.2))
  · intro ij hij
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hij).2⟩
  · intro ij hij kl hkl heq
    cases ij with
    | mk i j =>
      cases kl with
      | mk k l =>
        have hk : i = k := e.injective (Prod.mk.inj heq).1
        have hl : j = l := e.injective (Prod.mk.inj heq).2
        cases hk; cases hl; rfl
  · intro ij hij
    refine ⟨(e.symm ij.1,e.symm ij.2),?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simpa using (Finset.mem_filter.mp hij).2
    · simp

/-- The arbitrary-position gadget never duplicates any remaining variable. -/
theorem reindexed_gadget_occurrences_card_le {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (e : Equiv.Perm (Fin n))
    (a b : Fin n) (v : σ) :
    (occurrences (gadget (M.submatrix id e) a b) v).card ≤ (occurrences M v).card := by
  exact (gadget_occurrences_card_le (M.submatrix id e) a b v).trans_eq
    (reindex_occurrences_card M e v)

end PermanentOccurrence


-- BEGIN Solutions.PermanentEqualitySelector

/- Boolean selector used in Orzel, Srinivasan, Tavenas and Yehudayoff,
   The Algebraic Cost of a Boolean Sum, Observation 14. -/
namespace PermanentEqualitySelector

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommSemiring R]

def allTrue : ι → Bool := fun _ => true
def allFalse : ι → Bool := fun _ => false

def weight (y : ι → Bool) : R :=
  (∏ i, if y i then 1 else 0) + (∏ i, if y i then 0 else 1)

theorem true_product (y : ι → Bool) :
    (∏ i, if y i then (1 : R) else 0) = if y = allTrue then 1 else 0 := by
  classical
  by_cases h : y = allTrue
  · subst y; simp [allTrue]
  · have hex : ∃ i, y i = false := by
      by_contra hn
      apply h
      funext i
      have hi : y i ≠ false := fun hf => hn ⟨i,hf⟩
      cases he : y i <;> simp_all [allTrue]
    obtain ⟨i,hi⟩ := hex
    rw [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem false_product (y : ι → Bool) :
    (∏ i, if y i then (0 : R) else 1) = if y = allFalse then 1 else 0 := by
  classical
  by_cases h : y = allFalse
  · subst y; simp [allFalse]
  · have hex : ∃ i, y i = true := by
      by_contra hn
      apply h
      funext i
      have hi : y i ≠ true := fun ht => hn ⟨i,ht⟩
      cases he : y i <;> simp_all [allFalse]
    obtain ⟨i,hi⟩ := hex
    rw [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- The equality selector leaves only the all-zero and all-one assignments. -/
theorem sum_weight (f : (ι → Bool) → R) :
    ∑ y, weight y * f y = f allTrue + f allFalse := by
  classical
  simp only [weight,add_mul,Finset.sum_add_distrib,true_product,false_product]
  simp

end PermanentEqualitySelector


-- BEGIN Solutions.PermanentEqualityMatrix

/- The read-once permanent matrix of Orzel, Srinivasan, Tavenas and Yehudayoff,
   The Algebraic Cost of a Boolean Sum, Remark 16 (CC BY 4.0). -/

namespace PermanentEqualityMatrix

open MvPolynomial PermanentFoundation PermanentOccurrence
open Fin.NatCast

variable {σ : Type} [DecidableEq σ]

/-- A nonempty subset of a finite directed cycle that is closed under the
    successor operation contains the entire cycle. -/
theorem successor_closed_all {m : ℕ} (P : Fin (m + 1) → Prop)
    (hnext : ∀ i, P i → P (i + 1)) (i j : Fin (m + 1)) (hi : P i) : P j := by
  letI : NeZero (m + 1) := ⟨by omega⟩
  have hsteps : ∀ k : ℕ, P (i + (k : Fin (m + 1))) := by
    intro k
    induction k with
    | zero => simpa using hi
    | succ k ih => simpa [Nat.cast_succ, add_assoc] using hnext (i + (k : Fin (m + 1))) ih
  have hj := hsteps (j - i).val
  simpa using hj

/-- In a cycle cover of the gadget, using one inter-pair edge forces all
    inter-pair edges. The hypotheses describe the nonzero outgoing edges. -/
theorem cycle_cover_propagates {m : ℕ}
    (π : Equiv.Perm (Fin (m + 1) ⊕ Fin (m + 1)))
    (htop : ∀ i, π (.inl i) = .inl i ∨ π (.inl i) = .inl (i + 1) ∨
      π (.inl i) = .inr i)
    (hbottom : ∀ i, π (.inr i) = .inl i ∨ π (.inr i) = .inr i)
    (i : Fin (m + 1)) (hi : π (.inl i) = .inl (i + 1)) :
    ∀ j, π (.inl j) = .inl (j + 1) := by
  intro j
  apply successor_closed_all (fun j => π (.inl j) = .inl (j + 1)) ?_ i j hi
  intro k hk
  rcases htop (k + 1) with hself | hcycle | hcross
  · have he : (Sum.inl k : Fin (m + 1) ⊕ Fin (m + 1)) = .inl (k + 1) :=
      π.injective (hk.trans hself.symm)
    have hk' : k = k + 1 := Sum.inl.inj he
    simpa only [← hk'] using hself
  · exact hcycle
  · rcases hbottom (k + 1) with hback | hstay
    · have he := π.injective (hk.trans hback.symm)
      cases he
    · have he := π.injective (hcross.trans hstay.symm)
      cases he

/-- The paired vertices of the equality gadget. For two or more pairs, the
    upper vertices form a directed cycle; each lower vertex carries one variable.
    The permanent identity requires separately handling zero and one pair. -/
noncomputable def matrix {m : ℕ} (v : Fin m → σ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (MvPolynomial σ ℂ)
  | .inl i, .inl j => if i = j then C (-1) else if j.val = (i.val + 1) % m then C 1 else C 0
  | .inl i, .inr j => if i = j then C 1 else C 0
  | .inr i, .inl j => if i = j then C 1 else C 0
  | .inr i, .inr j => if i = j then X (v i) else C 0

theorem matrix_top_edges {m : ℕ} (v : Fin (m + 1) → σ) (i : Fin (m + 1))
    (c : Fin (m + 1) ⊕ Fin (m + 1)) (h : matrix v (.inl i) c ≠ 0) :
    c = .inl i ∨ c = .inl (i + 1) ∨ c = .inr i := by
  cases c with
  | inl j =>
    by_cases he : i = j
    · subst j; exact Or.inl rfl
    · by_cases hn : j.val = (i.val + 1) % (m + 1)
      · right; left; congr 1
        apply Fin.ext
        simpa [Fin.val_add, Fin.val_one, Nat.add_mod] using hn
      · exfalso
        apply h
        simp [matrix, he, hn]
  | inr j =>
    by_cases he : i = j
    · subst j; exact Or.inr (Or.inr rfl)
    · exfalso
      apply h
      simp [matrix, he]

theorem matrix_bottom_edges {m : ℕ} (v : Fin (m + 1) → σ) (i : Fin (m + 1))
    (c : Fin (m + 1) ⊕ Fin (m + 1)) (h : matrix v (.inr i) c ≠ 0) :
    c = .inl i ∨ c = .inr i := by
  cases c with
  | inl j =>
    by_cases he : i = j
    · subst j; exact Or.inl rfl
    · exfalso; apply h; simp [matrix, he]
  | inr j =>
    by_cases he : i = j
    · subst j; exact Or.inr rfl
    · exfalso; apply h; simp [matrix, he]

/-- A nonzero cycle-cover term that uses one cycle edge uses them all. -/
theorem matrix_cycle_cover_propagates {m : ℕ} (v : Fin (m + 1) → σ)
    (π : Equiv.Perm (Fin (m + 1) ⊕ Fin (m + 1)))
    (hnonzero : ∀ r, matrix v r (π r) ≠ 0)
    (i : Fin (m + 1)) (hi : π (.inl i) = .inl (i + 1)) :
    ∀ j, π (.inl j) = .inl (j + 1) :=
  cycle_cover_propagates π
    (fun j => matrix_top_edges v j (π (.inl j)) (hnonzero (.inl j)))
    (fun j => matrix_bottom_edges v j (π (.inr j)) (hnonzero (.inr j))) i hi

/-- Once the upper cycle is used, every lower vertex is forced to its loop. -/
theorem matrix_cycle_cover_bottom {m : ℕ} (v : Fin (m + 1) → σ)
    (π : Equiv.Perm (Fin (m + 1) ⊕ Fin (m + 1)))
    (hnonzero : ∀ r, matrix v r (π r) ≠ 0)
    (hall : ∀ j, π (.inl j) = .inl (j + 1)) (j : Fin (m + 1)) :
    π (.inr j) = .inr j := by
  letI : NeZero (m + 1) := ⟨by omega⟩
  rcases matrix_bottom_edges v j (π (.inr j)) (hnonzero (.inr j)) with h | h
  · have htop : π (.inl (j - 1)) = .inl j := by simpa using hall (j - 1)
    have he := π.injective (htop.trans h.symm)
    cases he
  · exact h

/-- In a cycle of at least two vertices, the successor is not the vertex itself. -/
theorem successor_ne_self {m : ℕ} (i : Fin (m + 2)) : i ≠ i + 1 := by
  letI : NeZero (m + 2) := ⟨by omega⟩
  intro h
  have h' : (0 : Fin (m + 2)) = 1 := by
    apply add_left_cancel (a := i)
    simpa using h
  exact zero_ne_one h'

/-- The full-cycle cover contributes exactly the product of the selectors. -/
theorem matrix_full_cycle_weight {m : ℕ} (v : Fin (m + 2) → σ)
    (π : Equiv.Perm (Fin (m + 2) ⊕ Fin (m + 2)))
    (htop : ∀ i, π (.inl i) = .inl (i + 1))
    (hbottom : ∀ i, π (.inr i) = .inr i) :
    (∏ r, matrix v r (π r)) = ∏ i, X (v i) := by
  rw [Fintype.prod_sum_type]
  have ht : ∀ i, matrix v (.inl i) (π (.inl i)) = 1 := by
    intro i
    rw [htop]
    simp only [matrix, if_neg (successor_ne_self i)]
    have hn : (i + 1).val = (i.val + 1) % (m + 2) := by
      simp [Fin.val_add, Fin.val_one, Nat.add_mod]
    simp [hn]
  have hb : ∀ i, matrix v (.inr i) (π (.inr i)) = X (v i) := by
    intro i
    rw [hbottom]
    simp [matrix]
  simp only [ht, hb, Finset.prod_const_one, one_mul]

/-- Without cycle edges, each pair is covered independently, either by its
    two loops or by the transposition between the pair's vertices. -/
theorem matrix_no_cycle_pair {m : ℕ} (v : Fin (m + 1) → σ)
    (π : Equiv.Perm (Fin (m + 1) ⊕ Fin (m + 1)))
    (hnonzero : ∀ r, matrix v r (π r) ≠ 0)
    (hnocycle : ∀ i, π (.inl i) ≠ .inl (i + 1)) (i : Fin (m + 1)) :
    (π (.inl i) = .inl i ∧ π (.inr i) = .inr i) ∨
      (π (.inl i) = .inr i ∧ π (.inr i) = .inl i) := by
  rcases matrix_top_edges v i (π (.inl i)) (hnonzero (.inl i)) with ht | ht | ht
  · left
    refine ⟨ht, ?_⟩
    rcases matrix_bottom_edges v i (π (.inr i)) (hnonzero (.inr i)) with hb | hb
    · have he := π.injective (ht.trans hb.symm)
      cases he
    · exact hb
  · exact (hnocycle i ht).elim
  · right
    refine ⟨ht, ?_⟩
    rcases matrix_bottom_edges v i (π (.inr i)) (hnonzero (.inr i)) with hb | hb
    · exact hb
    · have he := π.injective (ht.trans hb.symm)
      cases he

/-- The permutation that independently keeps or swaps each pair. -/
def pairPerm {α : Type} (b : α → Bool) : Equiv.Perm (α ⊕ α) where
  toFun
    | .inl i => if b i then .inl i else .inr i
    | .inr i => if b i then .inr i else .inl i
  invFun
    | .inl i => if b i then .inl i else .inr i
    | .inr i => if b i then .inr i else .inl i
  left_inv := by intro x; cases x with
    | inl i => cases h : b i <;> simp [h]
    | inr i => cases h : b i <;> simp [h]
  right_inv := by intro x; cases x with
    | inl i => cases h : b i <;> simp [h]
    | inr i => cases h : b i <;> simp [h]

theorem pairPerm_injective {α : Type} : Function.Injective (pairPerm : (α → Bool) → _) := by
  intro b c h
  funext i
  have hi := congrFun (congrArg (fun π : Equiv.Perm (α ⊕ α) => ⇑π) h) (.inl i)
  cases hb : b i <;> cases hc : c i <;> simp [pairPerm, hb, hc] at *

/-- A cover with no cycle edges is one of the independent pair permutations. -/
theorem matrix_no_cycle_eq_pairPerm {m : ℕ} (v : Fin (m + 1) → σ)
    (π : Equiv.Perm (Fin (m + 1) ⊕ Fin (m + 1)))
    (hnonzero : ∀ r, matrix v r (π r) ≠ 0)
    (hnocycle : ∀ i, π (.inl i) ≠ .inl (i + 1)) :
    ∃ b : Fin (m + 1) → Bool, π = pairPerm b := by
  classical
  let b : Fin (m + 1) → Bool := fun i => decide (π (.inl i) = .inl i)
  refine ⟨b, ?_⟩
  ext x
  cases x with
  | inl i =>
    rcases matrix_no_cycle_pair v π hnonzero hnocycle i with ⟨ht, hb⟩ | ⟨ht, hb⟩
    · simp [pairPerm, b, ht]
    · simp [pairPerm, b, ht]
  | inr i =>
    rcases matrix_no_cycle_pair v π hnonzero hnocycle i with ⟨ht, hb⟩ | ⟨ht, hb⟩
    · simp [pairPerm, b, ht, hb]
    · simp [pairPerm, b, ht, hb]

/-- The weight of a pair cover factors over its independent choices. -/
theorem matrix_pairPerm_weight {m : ℕ} (v : Fin m → σ) (b : Fin m → Bool) :
    (∏ r, matrix v r (pairPerm b r)) =
      ∏ i, if b i then -X (v i) else 1 := by
  rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases h : b i <;> simp [pairPerm, matrix, h]

/-- Adding all independent pair-cover weights gives the product of
    the factors `1 - X (v i)`. -/
theorem matrix_pairPerm_weight_sum {m : ℕ} (v : Fin m → σ) :
    (∑ b : Fin m → Bool, ∏ r, matrix v r (pairPerm b r)) =
      ∏ i, (1 - X (v i)) := by
  simp_rw [matrix_pairPerm_weight]
  rw [← Fintype.prod_sum (fun i (b : Bool) => if b then -X (v i) else 1)]
  apply Finset.prod_congr rfl
  intro i _
  simp [Fintype.sum_bool, sub_eq_add_neg, add_comm]

/-- The cover made of the upper directed cycle and all lower loops. -/
def fullCyclePerm (m : ℕ) : Equiv.Perm (Fin (m + 2) ⊕ Fin (m + 2)) :=
  Equiv.sumCongr
    { toFun := fun i => i + 1
      invFun := fun i => i - 1
      left_inv := by intro i; simp
      right_inv := by intro i; simp }
    (Equiv.refl _)

theorem fullCyclePerm_not_pairPerm {m : ℕ} (b : Fin (m + 2) → Bool) :
    fullCyclePerm m ≠ pairPerm b := by
  intro he
  let i : Fin (m + 2) := 0
  have h := congrFun (congrArg (fun π : Equiv.Perm (Fin (m + 2) ⊕ Fin (m + 2)) => ⇑π) he) (.inl i)
  cases hb : b i with
  | false => simp [fullCyclePerm, pairPerm, hb] at h
  | true =>
    have hi : i + 1 = i := by simpa [fullCyclePerm, pairPerm, hb] using h
    exact successor_ne_self i hi.symm

/-- All nonzero covers are either the full cycle or an independent pair cover. -/
theorem matrix_cover_classification {m : ℕ} (v : Fin (m + 2) → σ)
    (π : Equiv.Perm (Fin (m + 2) ⊕ Fin (m + 2)))
    (hnonzero : ∀ r, matrix v r (π r) ≠ 0) :
    π = fullCyclePerm m ∨ ∃ b, π = pairPerm b := by
  by_cases he : ∃ i, π (.inl i) = .inl (i + 1)
  · obtain ⟨i,hi⟩ := he
    have ht := matrix_cycle_cover_propagates v π hnonzero i hi
    have hb := matrix_cycle_cover_bottom v π hnonzero ht
    left
    ext r
    cases r with
    | inl i => simpa [fullCyclePerm] using ht i
    | inr i => simpa [fullCyclePerm] using hb i
  · right
    apply matrix_no_cycle_eq_pairPerm v π hnonzero
    simpa only [not_exists] using he

/-- The read-once equality matrix computes the equality selector polynomial. -/
theorem matrix_permanent {m : ℕ} (v : Fin (m + 2) → σ) :
    (matrix v).permanent = (∏ i, X (v i)) + ∏ i, (1 - X (v i)) := by
  classical
  let weight : Equiv.Perm (Fin (m + 2) ⊕ Fin (m + 2)) → MvPolynomial σ ℂ :=
    fun π => ∏ r, matrix v r (π r)
  let pairs := Finset.univ.image (pairPerm : (Fin (m + 2) → Bool) → _)
  let cyc := fullCyclePerm m
  have hdisjoint : Disjoint pairs {cyc} := by
    apply Finset.disjoint_singleton_right.mpr
    intro hm
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hm
    exact fullCyclePerm_not_pairPerm b hb.symm
  have hsupport : ∀ π ∉ pairs ∪ {cyc}, weight π = 0 := by
    intro π hπ
    by_contra hn
    have hnonzero : ∀ r, matrix v r (π r) ≠ 0 := by
      intro r hr
      apply hn
      exact Finset.prod_eq_zero (Finset.mem_univ r) hr
    rcases matrix_cover_classification v π hnonzero with hc | ⟨b,hb⟩
    · apply hπ
      simp [hc,cyc]
    · apply hπ
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb.symm⟩
  have hperm : (matrix v).permanent = ∑ π, weight π := by
    rw [← Matrix.permanent_transpose, Matrix.permanent]
    rfl
  rw [hperm, ← Finset.sum_subset (Finset.subset_univ (pairs ∪ {cyc}))]
  · rw [Finset.sum_union hdisjoint, Finset.sum_singleton]
    have hpairs : ∑ π ∈ pairs, weight π = ∏ i, (1 - X (v i)) := by
      rw [show pairs = Finset.univ.image pairPerm from rfl, Finset.sum_image]
      · exact matrix_pairPerm_weight_sum v
      · exact fun _ _ _ _ h => pairPerm_injective h
    have hcycle : weight cyc = ∏ i, X (v i) := by
      apply matrix_full_cycle_weight v (fullCyclePerm m)
      · intro i; rfl
      · intro i; rfl
    rw [hpairs,hcycle,add_comm]
  · intro π _ hπ
    exact hsupport π hπ

theorem matrix_isSubstMatrix {m : ℕ} (v : Fin m → σ) : IsSubstMatrix (matrix v) := by
  intro i j
  cases i <;> cases j <;> simp only [matrix] <;> split_ifs <;>
    first | exact IsSubstEntry.C _ | exact IsSubstEntry.X _

/-- The equality selector is a projection of a permanent of dimension `2m`. -/
theorem equality_isProjection {m : ℕ} (v : Fin (m + 2) → σ) :
    ResultantVNP.IsProjection ((∏ i, X (v i)) + ∏ i, (1 - X (v i)))
      (genericMatrix ((m + 2) + (m + 2))).permanent := by
  rw [← matrix_permanent v]
  exact (matrix_isSubstMatrix v).isProjection_permanent finSumFinEquiv.symm

/-- Under an injective labelling, each selector occurs in exactly one entry. -/
theorem matrix_occurrences {m : ℕ} (v : Fin m → σ) (hv : Function.Injective v)
    (i : Fin m) :
    occurrences (matrix v) (v i) = {((Sum.inr i : Fin m ⊕ Fin m), Sum.inr i)} := by
  classical
  ext ⟨r,c⟩
  simp only [occurrences, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  cases r with
  | inl r =>
    cases c <;> simp only [matrix, Prod.mk.injEq, Sum.inl_ne_inr, false_and, iff_false] <;>
      split_ifs <;> exact constant_ne_variable _ _
  | inr r =>
    cases c with
    | inl c =>
      simp only [matrix, Prod.mk.injEq, Sum.inl_ne_inr, and_false, iff_false]
      split_ifs <;> exact constant_ne_variable _ _
    | inr c =>
      simp only [matrix, Prod.mk.injEq, Sum.inr.injEq]
      by_cases h : r = c
      · subst c
        simp only [if_true, X_inj, and_self]
        exact ⟨fun he => hv he, congrArg v⟩
      · simp only [if_neg h]
        constructor
        · exact fun hh => (constant_ne_variable _ _ hh).elim
        · rintro ⟨rfl,rfl⟩
          exact (h rfl).elim

theorem matrix_occurrences_card {m : ℕ} (v : Fin m → σ) (hv : Function.Injective v)
    (i : Fin m) : (occurrences (matrix v) (v i)).card = 1 := by
  rw [matrix_occurrences v hv i, Finset.card_singleton]

/-- The equality matrix introduces no variables outside its given labels. -/
theorem matrix_occurrences_not_range {m : ℕ} (v : Fin m → σ) (w : σ)
    (hw : ∀ i, v i ≠ w) : occurrences (matrix v) w = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ⟨r,c⟩ hh
  have he := (Finset.mem_filter.mp hh).2
  cases r with
  | inl r =>
    cases c <;> simp only [matrix] at he <;> split_ifs at he <;>
      exact (constant_ne_variable _ w he).elim
  | inr r =>
    cases c with
    | inl c =>
      simp only [matrix] at he
      split_ifs at he <;> exact (constant_ne_variable _ w he).elim
    | inr c =>
      simp only [matrix] at he
      split_ifs at he with h
      · exact (hw r (MvPolynomial.X_injective he)).elim
      · exact (constant_ne_variable _ w he).elim

/-- For every number of selectors, including zero and one, the equality
    polynomial has a linear-size substitution matrix with at most one
    occurrence of each selector. -/
theorem equality_matrix_witness (m : ℕ) (v : Fin m → σ) (hv : Function.Injective v) :
    ∃ n ≤ 2 * m + 1, ∃ M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ),
      IsSubstMatrix M ∧ M.permanent = (∏ i, X (v i)) + ∏ i, (1 - X (v i)) ∧
      (∀ i, (occurrences M (v i)).card ≤ 1) ∧
      (∀ w, (∀ i, v i ≠ w) → occurrences M w = ∅) := by
  cases m with
  | zero =>
    refine ⟨1, by omega, Matrix.of (fun _ _ => C 2), ?_, ?_, ?_, ?_⟩
    · intro _ _; exact IsSubstEntry.C 2
    · rw [Matrix.permanent_unique]
      simp [map_ofNat]
      norm_num
    · intro i; exact Fin.elim0 i
    · intro w _
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ⟨r,c⟩ hh
      exact constant_ne_variable 2 w (Finset.mem_filter.mp hh).2
  | succ m =>
    cases m with
    | zero =>
      refine ⟨1, by omega, Matrix.of (fun _ _ => C 1), ?_, ?_, ?_, ?_⟩
      · intro _ _; exact IsSubstEntry.C 1
      · rw [Matrix.permanent_unique]
        change (1 : MvPolynomial σ ℂ) = (∏ i : Fin 1, X (v i)) + ∏ i : Fin 1, (1 - X (v i))
        simp only [Fin.prod_univ_one]
        ring
      · intro i
        have he : occurrences (Matrix.of (fun _ _ : Fin 1 => (C 1 : MvPolynomial σ ℂ))) (v i) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro ⟨r,c⟩ hh
          exact constant_ne_variable 1 (v i) (Finset.mem_filter.mp hh).2
        simpa only [map_one] using (show (occurrences (Matrix.of (fun _ _ : Fin 1 => (C 1 : MvPolynomial σ ℂ))) (v i)).card ≤ 1 by rw [he]; simp)
      · intro w _
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro ⟨r,c⟩ hh
        exact constant_ne_variable 1 w (Finset.mem_filter.mp hh).2
    | succ m =>
      let e : Fin ((m + 2) + (m + 2)) ≃ Fin (m + 2) ⊕ Fin (m + 2) := finSumFinEquiv.symm
      refine ⟨(m + 2) + (m + 2), by omega, (matrix v).submatrix e e, ?_, ?_, ?_, ?_⟩
      · exact (matrix_isSubstMatrix v).submatrix e e
      · rw [Matrix.permanent_submatrix_equiv e, matrix_permanent v]
      · intro i
        rw [equiv_occurrences_card (matrix v) e (v i), matrix_occurrences_card v hv i]
      · intro w hw
        apply Finset.card_eq_zero.mp
        rw [equiv_occurrences_card (matrix v) e w, matrix_occurrences_not_range v w hw]
        rfl


end PermanentEqualityMatrix

-- BEGIN Solutions.PermanentBooleanSum
/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/



/- Single-entry identity adapted from cslib-frontier e78796a1e0c0fe124f9130a84850a5104bbe5f14,
CslibFrontier/Foundations/Data/Matrix/Permanent/BooleanSum.lean.
The projection corollary below uses the mission definition. -/

namespace Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- Summing the two Boolean substitutions in one entry equals twice the half-substituted
permanent. The explicit hypothesis is satisfied when `2` is invertible. -/
theorem permanent_updateRow_update_zero_add_one (A : Matrix ι ι R) (i j : ι)
    (half : R) (hhalf : 2 * half = 1) :
    (A.updateRow i (Function.update (A i) j 0)).permanent +
        (A.updateRow i (Function.update (A i) j 1)).permanent =
      2 * (A.updateRow i (Function.update (A i) j half)).permanent := by
  have hrows : Function.update (A i) j 0 + Function.update (A i) j 1 =
      (2 : R) • Function.update (A i) j half := by
    funext k
    by_cases hk : k = j
    · subst k
      simp [hhalf]
    · simp [Function.update_of_ne hk, two_mul]
  rw [← permanent_updateRow_add, hrows, permanent_updateRow_smul]

/-- Simultaneous Boolean substitution in two entries in the same row.
The row is affine in its entries, so no cross term occurs. -/
theorem permanent_updateRow_two_boolean (A : Matrix ι ι R) (i j k : ι)
    (half : R) (hhalf : 2 * half = 1) :
    (A.updateRow i (Function.update (Function.update (A i) j 0) k 0)).permanent +
        (A.updateRow i (Function.update (Function.update (A i) j 1) k 1)).permanent =
      2 * (A.updateRow i (Function.update (Function.update (A i) j half) k half)).permanent := by
  have hrows : Function.update (Function.update (A i) j 0) k 0 +
      Function.update (Function.update (A i) j 1) k 1 =
      (2 : R) • Function.update (Function.update (A i) j half) k half := by
    funext x
    by_cases hxk : x = k
    · subst x; simp [hhalf]
    · by_cases hxj : x = j
      · subst x; simp [hxk,hhalf]
      · simp [hxk,hxj,two_mul]
  rw [← permanent_updateRow_add,hrows,permanent_updateRow_smul]

end Matrix

namespace PermanentFoundation
open MvPolynomial ResultantVNP
variable {σ : Type} {d : ℕ}

theorem isProjection_permanent_const (c : ℂ) :
    IsProjection (C c : MvPolynomial σ ℂ) (genericMatrix 1).permanent := by
  apply isProjection_permanent_iff_exists_substMatrix.mpr
  refine ⟨Matrix.of fun _ _ => C c,fun _ _ => .C c,?_⟩
  simp [Matrix.permanent_unique]

theorem IsSubstMatrix.updateEntry {M : Matrix (Fin d) (Fin d) (MvPolynomial σ ℂ)}
    (hM : IsSubstMatrix M) (i j : Fin d) (c : ℂ) :
    IsSubstMatrix (M.updateRow i (Function.update (M i) j (C c))) := by
  intro a b
  by_cases ha : a = i
  · subst a
    by_cases hb : b = j
    · subst b
      simpa only [Matrix.updateRow_self,Function.update_self] using IsSubstEntry.C (σ := σ) c
    · simpa only [Matrix.updateRow_self,Function.update_of_ne hb] using hM i b
  · simpa only [Matrix.updateRow_ne ha] using hM a b

theorem IsSubstMatrix.updateTwoEntries {M : Matrix (Fin d) (Fin d) (MvPolynomial σ ℂ)}
    (hM : IsSubstMatrix M) (i j k : Fin d) (c : ℂ) :
    IsSubstMatrix (M.updateRow i (Function.update (Function.update (M i) j (C c)) k (C c))) := by
  intro a b
  by_cases ha : a = i
  · subst a
    by_cases hk : b = k
    · subst b; simpa using IsSubstEntry.C (σ := σ) c
    · by_cases hj : b = j
      · subst b; simpa [hk] using IsSubstEntry.C (σ := σ) c
      · simpa [hk,hj] using hM i b
  · simpa only [Matrix.updateRow_ne ha] using hM a b

/-- Summing a Boolean selector occurring in one entry costs one extra matrix dimension.
The extra dimension absorbs the scalar two without changing the projection definition. -/
theorem single_entry_sum_isProjection {M : Matrix (Fin d) (Fin d) (MvPolynomial σ ℂ)}
    (hM : IsSubstMatrix M) (i j : Fin d) :
    IsProjection
      ((M.updateRow i (Function.update (M i) j 0)).permanent +
       (M.updateRow i (Function.update (M i) j 1)).permanent)
      (genericMatrix (d+1)).permanent := by
  let half : MvPolynomial σ ℂ := C (1/2 : ℂ)
  have hh : 2*half = 1 := by
    simpa only [half,map_mul,map_ofNat,map_one] using
      congrArg (C : ℂ → MvPolynomial σ ℂ) (by norm_num : (2 : ℂ)*(1/2) = 1)
  rw [Matrix.permanent_updateRow_update_zero_add_one M i j half hh,mul_comm]
  have hp := (hM.updateEntry i j (1/2)).isProjection_permanent (Equiv.refl _)
  simpa only [map_ofNat] using hp.permanent_mul (isProjection_permanent_const (σ := σ) 2)

/-- Eliminate a selector in two entries sharing a row with one extra dimension. -/
theorem same_row_sum_isProjection {M : Matrix (Fin d) (Fin d) (MvPolynomial σ ℂ)}
    (hM : IsSubstMatrix M) (i j k : Fin d) :
    IsProjection
      ((M.updateRow i (Function.update (Function.update (M i) j 0) k 0)).permanent +
       (M.updateRow i (Function.update (Function.update (M i) j 1) k 1)).permanent)
      (genericMatrix (d+1)).permanent := by
  let half : MvPolynomial σ ℂ := C (1/2 : ℂ)
  have hh : 2*half = 1 := by
    simpa only [half,map_mul,map_ofNat,map_one] using
      congrArg (C : ℂ → MvPolynomial σ ℂ) (by norm_num : (2 : ℂ)*(1/2) = 1)
  rw [Matrix.permanent_updateRow_two_boolean M i j k half hh,mul_comm]
  have hp := (hM.updateTwoEntries i j k (1/2)).isProjection_permanent (Equiv.refl _)
  simpa only [map_ofNat] using hp.permanent_mul (isProjection_permanent_const (σ := σ) 2)

/-- The same construction applies to entries sharing a column by transposition. -/
theorem same_column_sum_isProjection {M : Matrix (Fin d) (Fin d) (MvPolynomial σ ℂ)}
    (hM : IsSubstMatrix M) (i j k : Fin d) :
    IsProjection
      ((M.updateCol i (Function.update (Function.update (fun r => M r i) j 0) k 0)).permanent +
       (M.updateCol i (Function.update (Function.update (fun r => M r i) j 1) k 1)).permanent)
      (genericMatrix (d+1)).permanent := by
  have ht : IsSubstMatrix M.transpose := fun a b => hM b a
  have hp := same_row_sum_isProjection ht i j k
  simp only [Matrix.updateRow_transpose,Matrix.permanent_transpose] at hp
  have hrow : M.transpose i = (fun r => M r i) := rfl
  rw [hrow] at hp
  exact hp

end PermanentFoundation


-- BEGIN Solutions.PermanentSelectorSubstitution

namespace PermanentSelectorSubstitution
open MvPolynomial ResultantVNP PermanentFoundation PermanentGadgetMatrix PermanentGadgetReindex PermanentOccurrence

variable {σ : Type} [DecidableEq σ] {n : ℕ}

/-- Transfer a gadget witness to a standard `Fin m` index while preserving
    its permanent and all occurrence counts. -/
theorem finite_reindex_witness {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (e : Fin m ≃ α) (G : Matrix α α (MvPolynomial σ ℂ))
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (v : σ)
    (hG : IsSubstMatrix G) (he : occurrences G v = ∅)
    (hb : ∀ w,(occurrences G w).card ≤ (occurrences M w).card) :
    ∃ N : Matrix (Fin m) (Fin m) (MvPolynomial σ ℂ),
      IsSubstMatrix N ∧ N.permanent = G.permanent ∧ occurrences N v = ∅ ∧
        ∀ w,(occurrences N w).card ≤ (occurrences M w).card := by
  refine ⟨G.submatrix e e,hG.submatrix e e,Matrix.permanent_submatrix_equiv e G,?_,?_⟩
  · apply Finset.card_eq_zero.mp
    rw [equiv_occurrences_card G e v,he]
    rfl
  · intro w
    rw [equiv_occurrences_card G e w]
    exact hb w

/-- Substitute one variable by a field constant and leave all others fixed. -/
noncomputable def substitute (v : σ) (z : ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval (fun x => if x = v then C z else X x)

@[simp] theorem substitute_C (v : σ) (z c : ℂ) : substitute v z (C c) = C c := by
  simp [substitute]

@[simp] theorem substitute_X (v x : σ) (z : ℂ) :
    substitute v z (X x) = if x = v then C z else X x := by
  simp [substitute]

theorem substitute_entry_ne {p : MvPolynomial σ ℂ} (hp : IsSubstEntry p)
    (v : σ) (z : ℂ) (hne : p ≠ X v) : substitute v z p = p := by
  obtain ⟨s,rfl⟩ := hp
  cases s with
  | inl x =>
    have hx : x ≠ v := by intro h; subst x; exact hne rfl
    simp [hx]
  | inr c => simp

theorem substitute_matrix (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (v : σ) (i j k l : Fin n) (z : ℂ)
    (hfirst : M i j = X v) (hsecond : M k l = X v)
    (hcover : ∀ r c, M r c = X v → (r = i ∧ c = j) ∨ (r = k ∧ c = l)) :
    M.map (substitute v z) = setTwo M i j k l (C z) := by
  apply Matrix.ext
  intro r c
  by_cases h : (r = i ∧ c = j) ∨ (r = k ∧ c = l)
  · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [setTwo,hfirst,hsecond]
  · have hn : M r c ≠ X v := fun hv => h (hcover r c hv)
    simp only [Matrix.map_apply,setTwo,Matrix.of_apply,if_neg h]
    exact substitute_entry_ne (hM r c) v z hn

/-- The gadget represents the sum over the two Boolean values of a selector. -/
theorem selector_sum_isProjection (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (v : σ) (i j k l : Fin n)
    (hik : i ≠ k) (hjl : j ≠ l)
    (hfirst : M i j = X v) (hsecond : M k l = X v)
    (hcover : ∀ r c, M r c = X v → (r = i ∧ c = j) ∨ (r = k ∧ c = l)) :
    IsProjection (substitute v 0 M.permanent + substitute v 1 M.permanent)
      (genericMatrix (3+n)).permanent := by
  have h0 := substitute_matrix M hM v i j k l 0 hfirst hsecond hcover
  have h1 := substitute_matrix M hM v i j k l 1 hfirst hsecond hcover
  have hp := boolean_sum_arbitrary_positions M hM i j k l hik hjl
  rw [AlgHom.map_permanent,h0,AlgHom.map_permanent,h1]
  simpa only [map_zero,map_one] using hp

/-- Explicit one-occurrence gadget: replace the occurrence by one half and
    add a one-by-one block of weight two. -/
noncomputable def oneOccurrenceGadget
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (i j : Fin n) :
    Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) (MvPolynomial σ ℂ) :=
  Matrix.fromBlocks (Matrix.of fun _ _ => 2) 0 0
    (M.updateRow i (Function.update (M i) j (C (1/2 : ℂ))))

theorem oneOccurrenceGadget_entries (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (i j : Fin n) : IsSubstMatrix (oneOccurrenceGadget M i j) := by
  apply IsSubstMatrix.fromBlocks
  · intro _ _
    simpa only [Matrix.of_apply,map_ofNat] using (IsSubstEntry.C (σ := σ) 2)
  · exact IsSubstMatrix.zero
  · exact IsSubstMatrix.zero
  · exact hM.updateEntry i j (1/2)

theorem oneOccurrenceGadget_sum (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (v : σ) (i j : Fin n)
    (hentry : M i j = X v) (hcover : ∀ r c, M r c = X v → r = i ∧ c = j) :
    (oneOccurrenceGadget M i j).permanent =
      substitute v 0 M.permanent + substitute v 1 M.permanent := by
  have hc : ∀ r c, M r c = X v → (r = i ∧ c = j) ∨ (r = i ∧ c = j) :=
    fun r c h => Or.inl (hcover r c h)
  have h0 := substitute_matrix M hM v i j i j 0 hentry hentry hc
  have h1 := substitute_matrix M hM v i j i j 1 hentry hentry hc
  have hz : setTwo M i j i j (0 : MvPolynomial σ ℂ) =
      M.updateRow i (Function.update (M i) j 0) := by
    apply Matrix.ext
    intro r c
    by_cases hr : r = i <;> by_cases hc : c = j <;> simp [setTwo,Matrix.updateRow,Function.update,hr,hc]
  have ho : setTwo M i j i j (1 : MvPolynomial σ ℂ) =
      M.updateRow i (Function.update (M i) j 1) := by
    apply Matrix.ext
    intro r c
    by_cases hr : r = i <;> by_cases hc : c = j <;> simp [setTwo,Matrix.updateRow,Function.update,hr,hc]
  let half : MvPolynomial σ ℂ := C (1/2 : ℂ)
  have hh : 2*half = 1 := by
    simpa only [half,map_mul,map_ofNat,map_one] using
      congrArg (C : ℂ → MvPolynomial σ ℂ) (by norm_num : (2 : ℂ)*(1/2) = 1)
  rw [AlgHom.map_permanent,h0,AlgHom.map_permanent,h1]
  simp only [map_zero,map_one,hz,ho]
  rw [Matrix.permanent_updateRow_update_zero_add_one M i j half hh]
  rw [oneOccurrenceGadget,Matrix.permanent_fromBlocks_zero,Matrix.permanent_unique]
  simp [half]

theorem oneOccurrenceGadget_occurrences (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (i j : Fin n) (w : σ) :
    occurrences (oneOccurrenceGadget M i j) w ⊆
      (occurrences M w).image (fun ij => (Sum.inr ij.1,Sum.inr ij.2)) := by
  intro ⟨r,c⟩ h
  have hv : oneOccurrenceGadget M i j r c = X w := (Finset.mem_filter.mp h).2
  cases r with
  | inl r =>
    cases c with
    | inl c =>
      have hh : (C (2:ℂ) : MvPolynomial σ ℂ) = X w := by
        simpa only [map_ofNat] using (show (2 : MvPolynomial σ ℂ) = X w by simpa [oneOccurrenceGadget] using hv)
      exact (constant_ne_variable 2 w hh).elim
    | inr c =>
      have hh : (0 : MvPolynomial σ ℂ) = X w := by simpa [oneOccurrenceGadget] using hv
      exact (X_ne_zero w hh.symm).elim
  | inr r =>
    cases c with
    | inl c =>
      have hh : (0 : MvPolynomial σ ℂ) = X w := by simpa [oneOccurrenceGadget] using hv
      exact (X_ne_zero w hh.symm).elim
    | inr c =>
      change (M.updateRow i (Function.update (M i) j (C (1/2 : ℂ)))) r c = X w at hv
      by_cases hr : r = i
      · subst r
        by_cases hc : c = j
        · subst c
          simp only [Matrix.updateRow_self,Function.update_self] at hv
          exact (constant_ne_variable (1/2) w hv).elim
        · simp only [Matrix.updateRow_self,Function.update_of_ne hc] at hv
          exact Finset.mem_image.mpr ⟨(i,c),by simp [occurrences,hv],rfl⟩
      · simp only [Matrix.updateRow_ne hr] at hv
        exact Finset.mem_image.mpr ⟨(r,c),by simp [occurrences,hv],rfl⟩

theorem oneOccurrenceGadget_card_le (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (i j : Fin n) (w : σ) :
    (occurrences (oneOccurrenceGadget M i j) w).card ≤ (occurrences M w).card :=
  (Finset.card_le_card (oneOccurrenceGadget_occurrences M i j w)).trans Finset.card_image_le

theorem oneOccurrenceGadget_eliminates (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (v : σ) (i j : Fin n) (hcover : ∀ r c, M r c = X v → r = i ∧ c = j) :
    occurrences (oneOccurrenceGadget M i j) v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ⟨r,c⟩ h
  have hv := (Finset.mem_filter.mp h).2
  obtain ⟨⟨r',c'⟩,hmem,heq⟩ := Finset.mem_image.mp (oneOccurrenceGadget_occurrences M i j v h)
  have hm : M r' c' = X v := (Finset.mem_filter.mp hmem).2
  obtain ⟨rfl,rfl⟩ := hcover r' c' hm
  cases heq
  have hh : (C (1/2 : ℂ) : MvPolynomial σ ℂ) = X v := by
    simpa [oneOccurrenceGadget] using hv
  exact constant_ne_variable (1/2) v hh

theorem oneOccurrenceGadget_with_invariant (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (v : σ) (i j : Fin n)
    (hentry : M i j = X v) (hcover : ∀ r c, M r c = X v → r = i ∧ c = j) :
    IsSubstMatrix (oneOccurrenceGadget M i j) ∧
    (oneOccurrenceGadget M i j).permanent = substitute v 0 M.permanent + substitute v 1 M.permanent ∧
    occurrences (oneOccurrenceGadget M i j) v = ∅ ∧
    ∀ w, (occurrences (oneOccurrenceGadget M i j) w).card ≤ (occurrences M w).card :=
  ⟨oneOccurrenceGadget_entries M hM i j,oneOccurrenceGadget_sum M hM v i j hentry hcover,
    oneOccurrenceGadget_eliminates M v i j hcover,oneOccurrenceGadget_card_le M i j⟩

/-- When the selector does not occur, a scalar block supplies the factor two. -/
noncomputable def absentOccurrenceGadget (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) :
    Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) (MvPolynomial σ ℂ) :=
  Matrix.fromBlocks (Matrix.of fun _ _ => 2) 0 0 M

theorem absentOccurrenceGadget_entries (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) : IsSubstMatrix (absentOccurrenceGadget M) := by
  apply IsSubstMatrix.fromBlocks
  · intro _ _
    simpa only [Matrix.of_apply,map_ofNat] using (IsSubstEntry.C (σ := σ) 2)
  · exact IsSubstMatrix.zero
  · exact IsSubstMatrix.zero
  · exact hM

theorem absentOccurrenceGadget_sum (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (v : σ) (habs : ∀ i j, M i j ≠ X v) :
    (absentOccurrenceGadget M).permanent =
      substitute v 0 M.permanent + substitute v 1 M.permanent := by
  have hmap (z : ℂ) : M.map (substitute v z) = M := by
    apply Matrix.ext
    intro i j
    exact substitute_entry_ne (hM i j) v z (habs i j)
  rw [AlgHom.map_permanent,hmap 0,AlgHom.map_permanent,hmap 1]
  rw [absentOccurrenceGadget,Matrix.permanent_fromBlocks_zero,Matrix.permanent_unique]
  simp [two_mul]

theorem absentOccurrenceGadget_occurrences (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (w : σ) : occurrences (absentOccurrenceGadget M) w ⊆
      (occurrences M w).image (fun ij => (Sum.inr ij.1,Sum.inr ij.2)) := by
  intro ⟨r,c⟩ h
  have hv : absentOccurrenceGadget M r c = X w := (Finset.mem_filter.mp h).2
  cases r with
  | inl r =>
    cases c with
    | inl c =>
      have hh : (C (2:ℂ) : MvPolynomial σ ℂ) = X w := by
        simpa only [map_ofNat] using (show (2 : MvPolynomial σ ℂ) = X w by simpa [absentOccurrenceGadget] using hv)
      exact (constant_ne_variable 2 w hh).elim
    | inr c =>
      have hh : (0 : MvPolynomial σ ℂ) = X w := by simpa [absentOccurrenceGadget] using hv
      exact (X_ne_zero w hh.symm).elim
  | inr r =>
    cases c with
    | inl c =>
      have hh : (0 : MvPolynomial σ ℂ) = X w := by simpa [absentOccurrenceGadget] using hv
      exact (X_ne_zero w hh.symm).elim
    | inr c =>
      change M r c = X w at hv
      exact Finset.mem_image.mpr ⟨(r,c),by simp [occurrences,hv],rfl⟩

theorem absentOccurrenceGadget_with_invariant (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (v : σ) (habs : ∀ i j, M i j ≠ X v) :
    IsSubstMatrix (absentOccurrenceGadget M) ∧
    (absentOccurrenceGadget M).permanent = substitute v 0 M.permanent + substitute v 1 M.permanent ∧
    occurrences (absentOccurrenceGadget M) v = ∅ ∧
    ∀ w, (occurrences (absentOccurrenceGadget M) w).card ≤ (occurrences M w).card := by
  refine ⟨absentOccurrenceGadget_entries M hM,absentOccurrenceGadget_sum M hM v habs,?_,?_⟩
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ij hij
    obtain ⟨⟨r,c⟩,hm,_⟩ := Finset.mem_image.mp (absentOccurrenceGadget_occurrences M v hij)
    exact habs r c (Finset.mem_filter.mp hm).2
  · intro w
    exact (Finset.card_le_card (absentOccurrenceGadget_occurrences M w)).trans Finset.card_image_le

/-- Replacing two matrix entries by constants cannot introduce variable occurrences. -/
theorem setTwo_constant_occurrences (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (i j k l : Fin n) (z : ℂ) (w : σ) :
    occurrences (setTwo M i j k l (C z)) w ⊆ occurrences M w := by
  intro ⟨r,c⟩ h
  have hv := (Finset.mem_filter.mp h).2
  change (if (r = i ∧ c = j) ∨ (r = k ∧ c = l) then C z else M r c) = X w at hv
  split_ifs at hv
  · exact (constant_ne_variable z w hv).elim
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩

theorem setTwo_constant_eliminates (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (i j k l : Fin n) (z : ℂ) (v : σ)
    (hcover : ∀ r c, M r c = X v → (r = i ∧ c = j) ∨ (r = k ∧ c = l)) :
    occurrences (setTwo M i j k l (C z)) v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ⟨r,c⟩ h
  have hv := (Finset.mem_filter.mp h).2
  have hm : M r c = X v := (Finset.mem_filter.mp (setTwo_constant_occurrences M i j k l z v h)).2
  have hc := hcover r c hm
  change (if (r = i ∧ c = j) ∨ (r = k ∧ c = l) then C z else M r c) = X v at hv
  rw [if_pos hc] at hv
  exact constant_ne_variable z v hv

noncomputable def sameRowGadget (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (i j k : Fin n) := absentOccurrenceGadget (setTwo M i j i k (C (1/2 : ℂ)))

theorem sameRowGadget_with_invariant (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (v : σ) (i j k : Fin n)
    (hfirst : M i j = X v) (hsecond : M i k = X v)
    (hcover : ∀ r c, M r c = X v → (r = i ∧ c = j) ∨ (r = i ∧ c = k)) :
    IsSubstMatrix (sameRowGadget M i j k) ∧
    (sameRowGadget M i j k).permanent = substitute v 0 M.permanent + substitute v 1 M.permanent ∧
    occurrences (sameRowGadget M i j k) v = ∅ ∧
    ∀ w, (occurrences (sameRowGadget M i j k) w).card ≤ (occurrences M w).card := by
  let H := setTwo M i j i k (C (1/2 : ℂ))
  have hH : IsSubstMatrix H := by
    intro r c
    change IsSubstEntry (if (r = i ∧ c = j) ∨ (r = i ∧ c = k) then C (1/2 : ℂ) else M r c)
    split_ifs <;> first | exact IsSubstEntry.C _ | exact hM r c
  have hupdate (z : ℂ) : setTwo M i j i k (C z) =
      M.updateRow i (Function.update (Function.update (M i) j (C z)) k (C z)) := by
    apply Matrix.ext
    intro r c
    by_cases hr : r = i <;> by_cases hj : c = j <;> by_cases hk : c = k <;>
      simp [setTwo,Matrix.updateRow,Function.update,hr,hj,hk]
  have h0 := substitute_matrix M hM v i j i k 0 hfirst hsecond hcover
  have h1 := substitute_matrix M hM v i j i k 1 hfirst hsecond hcover
  have hhalf : 2*(C (1/2 : ℂ) : MvPolynomial σ ℂ) = 1 := by
    simpa only [map_mul,map_ofNat,map_one] using
      congrArg (C : ℂ → MvPolynomial σ ℂ) (by norm_num : (2 : ℂ)*(1/2)=1)
  refine ⟨absentOccurrenceGadget_entries H hH,?_,?_,?_⟩
  · rw [AlgHom.map_permanent,h0,AlgHom.map_permanent,h1,hupdate 0,hupdate 1]
    simp only [map_zero,map_one]
    rw [Matrix.permanent_updateRow_two_boolean M i j k _ hhalf]
    change (absentOccurrenceGadget H).permanent = _
    rw [absentOccurrenceGadget,Matrix.permanent_fromBlocks_zero,Matrix.permanent_unique]
    simp only [Matrix.of_apply]
    congr 1
    exact congrArg Matrix.permanent (hupdate (1/2))
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ij hij
    obtain ⟨q,hq,_⟩ := Finset.mem_image.mp (absentOccurrenceGadget_occurrences H v hij)
    have hz := setTwo_constant_eliminates M i j i k (1/2) v hcover
    change occurrences H v = ∅ at hz
    rw [hz] at hq
    exact Finset.notMem_empty _ hq
  · intro w
    calc
      (occurrences (sameRowGadget M i j k) w).card ≤ (occurrences H w).card :=
        (Finset.card_le_card (absentOccurrenceGadget_occurrences H w)).trans Finset.card_image_le
      _ ≤ (occurrences M w).card := Finset.card_le_card (setTwo_constant_occurrences M i j i k (1/2) w)

/-- The shared-column case follows from the shared-row gadget by transposition. -/
theorem sameColumnGadget_with_invariant (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (v : σ) (i j k : Fin n)
    (hfirst : M j i = X v) (hsecond : M k i = X v)
    (hcover : ∀ r c, M r c = X v → (r = j ∧ c = i) ∨ (r = k ∧ c = i)) :
    IsSubstMatrix (sameRowGadget M.transpose i j k) ∧
    (sameRowGadget M.transpose i j k).permanent = substitute v 0 M.permanent + substitute v 1 M.permanent ∧
    occurrences (sameRowGadget M.transpose i j k) v = ∅ ∧
    ∀ w, (occurrences (sameRowGadget M.transpose i j k) w).card ≤ (occurrences M w).card := by
  have ht : IsSubstMatrix M.transpose := fun r c => hM c r
  have hc : ∀ r c, M.transpose r c = X v → (r = i ∧ c = j) ∨ (r = i ∧ c = k) := by
    intro r c h
    rcases hcover c r h with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Or.inl ⟨h2,h1⟩
    · exact Or.inr ⟨h2,h1⟩
  obtain ⟨he,hs,hv,ho⟩ := sameRowGadget_with_invariant M.transpose ht v i j k hfirst hsecond hc
  refine ⟨he,?_,hv,?_⟩
  · simpa only [Matrix.permanent_transpose] using hs
  · intro w
    exact (ho w).trans_eq (transpose_occurrences_card M w)

/-- Standardize an explicit sum-indexed gadget to `Fin (d+n)`. -/
theorem standardize_gadget {d : ℕ} (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (v : σ) (G : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) (MvPolynomial σ ℂ))
    (hd : d ≤ 3) (hG : IsSubstMatrix G)
    (hs : G.permanent = substitute v 0 M.permanent + substitute v 1 M.permanent)
    (he : occurrences G v = ∅)
    (hb : ∀ w,(occurrences G w).card ≤ (occurrences M w).card) :
    ∃ m ≤ n+3, ∃ N : Matrix (Fin m) (Fin m) (MvPolynomial σ ℂ),
      IsSubstMatrix N ∧ N.permanent = substitute v 0 M.permanent + substitute v 1 M.permanent ∧
      occurrences N v = ∅ ∧ ∀ w,(occurrences N w).card ≤ (occurrences M w).card := by
  obtain ⟨N,hN,hp,hn,hb'⟩ := finite_reindex_witness finSumFinEquiv.symm G M v hG he hb
  exact ⟨d+n,by omega,N,hN,hp.trans hs,hn,hb'⟩

/-- The explicit gadget simultaneously computes the Boolean sum, eliminates
    the selected variable, and preserves the occurrence bounds of all others. -/
theorem selector_sum_with_occurrence_invariant
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (v : σ) (i j k l : Fin n)
    (hik : i ≠ k) (hjl : j ≠ l)
    (hfirst : M i j = X v) (hsecond : M k l = X v)
    (hcover : ∀ r c, M r c = X v → (r = i ∧ c = j) ∨ (r = k ∧ c = l)) :
    ∃ e : Equiv.Perm (Fin n),
      let G := gadget (M.submatrix id e) i k
      IsSubstMatrix G ∧
      G.permanent = substitute v 0 M.permanent + substitute v 1 M.permanent ∧
      occurrences G v = ∅ ∧
      ∀ w, (occurrences G w).card ≤ (occurrences M w).card := by
  obtain ⟨e,hei,hek⟩ := exists_two_point_permutation i k j l hik hjl
  refine ⟨e,gadget_entries (hM.submatrix id e) i k,?_,?_,?_⟩
  · rw [gadget_boolean_sum _ i k hik,
      reindex_cleared M i j k l e hei hek,reindex_restored M i j k l hik e hei hek]
    have hperm (N : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) :
        (N.submatrix id e).permanent = N.permanent :=
      Matrix.permanent_submatrix_equiv_equiv (Equiv.refl _) e N
    simp only [hperm,AlgHom.map_permanent,substitute_matrix M hM v i j k l 0 hfirst hsecond hcover,
      substitute_matrix M hM v i j k l 1 hfirst hsecond hcover,map_zero,map_one]
  · apply gadget_eliminates
    intro r c hv
    have hc := hcover r (e c) hv
    rcases hc with ⟨hr,hc⟩ | ⟨hr,hc⟩
    · exact Or.inl ⟨hr,e.injective (hc.trans hei.symm)⟩
    · exact Or.inr ⟨hr,e.injective (hc.trans hek.symm)⟩
  · intro w
    exact reindexed_gadget_occurrences_card_le M e i k w

/-- Eliminate a selector with zero, one, or two explicitly specified occurrences. -/
theorem eliminate_two_covered (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (v : σ) (i j k l : Fin n)
    (hfirst : M i j = X v) (hsecond : M k l = X v)
    (hcover : ∀ r c, M r c = X v → (r = i ∧ c = j) ∨ (r = k ∧ c = l)) :
    ∃ m ≤ n+3, ∃ N : Matrix (Fin m) (Fin m) (MvPolynomial σ ℂ),
      IsSubstMatrix N ∧ N.permanent = substitute v 0 M.permanent + substitute v 1 M.permanent ∧
      occurrences N v = ∅ ∧ ∀ w,(occurrences N w).card ≤ (occurrences M w).card := by
  by_cases hr : i = k
  · subst k
    obtain ⟨he,hs,hv,ho⟩ := sameRowGadget_with_invariant M hM v i j l hfirst hsecond hcover
    exact standardize_gadget M v _ (by decide) he hs hv ho
  · by_cases hc : j = l
    · subst l
      obtain ⟨he,hs,hv,ho⟩ := sameColumnGadget_with_invariant M hM v j i k hfirst hsecond hcover
      exact standardize_gadget M v _ (by decide) he hs hv ho
    · obtain ⟨e,he,hs,hv,ho⟩ :=
        selector_sum_with_occurrence_invariant M hM v i j k l hr hc hfirst hsecond hcover
      exact standardize_gadget M v _ (by decide) he hs hv ho

/-- Eliminate any selector occurring at most twice, adding at most three
    dimensions and preserving all other occurrence bounds. -/
theorem eliminate_at_most_two (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (v : σ) (hcard : (occurrences M v).card ≤ 2) :
    ∃ m ≤ n+3, ∃ N : Matrix (Fin m) (Fin m) (MvPolynomial σ ℂ),
      IsSubstMatrix N ∧ N.permanent = substitute v 0 M.permanent + substitute v 1 M.permanent ∧
      occurrences N v = ∅ ∧ ∀ w,(occurrences N w).card ≤ (occurrences M w).card := by
  by_cases hz : (occurrences M v).card = 0
  · have hempty := Finset.card_eq_zero.mp hz
    have habs : ∀ i j, M i j ≠ X v := by
      intro i j h
      have hm : (i,j) ∈ occurrences M v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
      rw [hempty] at hm
      exact Finset.notMem_empty _ hm
    obtain ⟨he,hs,hv,ho⟩ := absentOccurrenceGadget_with_invariant M hM v habs
    exact standardize_gadget M v _ (by decide) he hs hv ho
  · by_cases ho : (occurrences M v).card = 1
    · obtain ⟨⟨i,j⟩,hset⟩ := Finset.card_eq_one.mp ho
      have hentry : M i j = X v := by
        have hm : (i,j) ∈ occurrences M v := by rw [hset]; simp
        exact (Finset.mem_filter.mp hm).2
      have hcover : ∀ r c, M r c = X v → r = i ∧ c = j := by
        intro r c h
        have hm : (r,c) ∈ occurrences M v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
        rw [hset] at hm
        exact Prod.mk.inj (Finset.mem_singleton.mp hm)
      obtain ⟨he,hs,hv,hbound⟩ := oneOccurrenceGadget_with_invariant M hM v i j hentry hcover
      exact standardize_gadget M v _ (by decide) he hs hv hbound
    · have ht : (occurrences M v).card = 2 := by omega
      obtain ⟨⟨i,j⟩,⟨k,l⟩,hne,hset⟩ := Finset.card_eq_two.mp ht
      have hfirst : M i j = X v := by
        have hm : (i,j) ∈ occurrences M v := by rw [hset]; simp
        exact (Finset.mem_filter.mp hm).2
      have hsecond : M k l = X v := by
        have hm : (k,l) ∈ occurrences M v := by rw [hset]; simp
        exact (Finset.mem_filter.mp hm).2
      have hcover : ∀ r c, M r c = X v → (r = i ∧ c = j) ∨ (r = k ∧ c = l) := by
        intro r c h
        have hm : (r,c) ∈ occurrences M v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
        rw [hset] at hm
        rcases Finset.mem_insert.mp hm with he | he
        · exact Or.inl (Prod.mk.inj he)
        · exact Or.inr (Prod.mk.inj (Finset.mem_singleton.mp he))
      exact eliminate_two_covered M hM v i j k l hfirst hsecond hcover


end PermanentSelectorSubstitution


-- BEGIN Solutions.PermanentSelectorIteration

namespace PermanentSelectorIteration
open MvPolynomial ResultantVNP PermanentFoundation PermanentOccurrence PermanentSelectorSubstitution

variable {σ : Type} [DecidableEq σ]

/-- Successively sum a polynomial over the Boolean values of the listed variables. -/
noncomputable def booleanSum : List σ → MvPolynomial σ ℂ → MvPolynomial σ ℂ
  | [], p => p
  | v :: vs, p => booleanSum vs (substitute v 0 p + substitute v 1 p)

@[simp] theorem booleanSum_add (vs : List σ) (p q : MvPolynomial σ ℂ) :
    booleanSum vs (p+q) = booleanSum vs p + booleanSum vs q := by
  induction vs generalizing p q with
  | nil => rfl
  | cons v vs ih =>
    simp only [booleanSum,map_add]
    rw [show substitute v 0 p + substitute v 0 q + (substitute v 1 p + substitute v 1 q) =
      (substitute v 0 p + substitute v 1 p) + (substitute v 0 q + substitute v 1 q) by ac_rfl]
    exact ih _ _

@[simp] theorem booleanSum_zero (vs : List σ) : booleanSum vs 0 = 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [booleanSum,ih]

theorem booleanSum_append (us vs : List σ) (p : MvPolynomial σ ℂ) :
    booleanSum (us ++ vs) p = booleanSum vs (booleanSum us p) := by
  induction us generalizing p with
  | nil => rfl
  | cons u us ih => simpa only [List.cons_append,booleanSum] using ih _

/-- Substituting distinct variables commutes. -/
theorem substitute_commute (u v : σ) (huv : u ≠ v) (a b : ℂ)
    (p : MvPolynomial σ ℂ) :
    substitute u a (substitute v b p) = substitute v b (substitute u a p) := by
  have he : (substitute u a).comp (substitute v b) =
      (substitute v b).comp (substitute u a) := by
    apply MvPolynomial.algHom_ext
    intro x
    by_cases hu : x = u <;> by_cases hv : x = v <;>
      simp [AlgHom.comp_apply,substitute_X,substitute_C,hu,hv,huv,Ne.symm huv] at *
  exact DFunLike.congr_fun he p

/-- A substitution commutes with summation over other variables. -/
theorem substitute_booleanSum (u : σ) (a : ℂ) (vs : List σ) (hu : u ∉ vs)
    (p : MvPolynomial σ ℂ) :
    substitute u a (booleanSum vs p) = booleanSum vs (substitute u a p) := by
  induction vs generalizing p with
  | nil => rfl
  | cons v vs ih =>
    have huv : u ≠ v := by simp only [List.mem_cons,not_or] at hu; exact hu.1
    have hut : u ∉ vs := by simp only [List.mem_cons,not_or] at hu; exact hu.2
    simp only [booleanSum]
    rw [ih hut, map_add, substitute_commute u v huv a 0,substitute_commute u v huv a 1]

/-- With distinct variables, the first Boolean sum can be taken last. -/
theorem booleanSum_cons_outer (v : σ) (vs : List σ) (hv : v ∉ vs)
    (p : MvPolynomial σ ℂ) :
    booleanSum (v :: vs) p =
      substitute v 0 (booleanSum vs p) + substitute v 1 (booleanSum vs p) := by
  simp only [booleanSum,booleanSum_add,substitute_booleanSum v 0 vs hv,
    substitute_booleanSum v 1 vs hv]

/-- Boolean summation is independent of the order of the selectors. -/
theorem booleanSum_perm {us vs : List σ} (h : us.Perm vs) (p : MvPolynomial σ ℂ) :
    booleanSum us p = booleanSum vs p := by
  induction h generalizing p with
  | nil => rfl
  | cons v h ih =>
    simp only [booleanSum]
    exact ih _
  | swap u v vs =>
    by_cases huv : u = v
    · subst v; rfl
    · simp only [booleanSum,map_add]
      rw [substitute_commute u v huv 0 0,substitute_commute u v huv 1 0,
        substitute_commute u v huv 0 1,substitute_commute u v huv 1 1]
      apply congrArg (booleanSum vs)
      ac_rfl
  | trans h1 h2 ih1 ih2 => exact (ih1 p).trans (ih2 p)

/-- Evaluate a list of selector assignments in the same order as `booleanSum`. -/
noncomputable def assignmentValue : (vs : List σ) → (Fin vs.length → Bool) →
    MvPolynomial σ ℂ → MvPolynomial σ ℂ
  | [], _, p => p
  | v :: vs, bits, p =>
      assignmentValue vs (fun i => bits i.succ) (substitute v (if bits 0 then 1 else 0) p)

/-- The sequential assignment as an algebra homomorphism. -/
noncomputable def assignmentHom : (vs : List σ) → (Fin vs.length → Bool) →
    (MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
  | [], _ => AlgHom.id ℂ (MvPolynomial σ ℂ)
  | v :: vs, bits => (assignmentHom vs (fun i => bits i.succ)).comp
      (substitute v (if bits 0 then 1 else 0))

theorem assignmentHom_apply (vs : List σ) (bits : Fin vs.length → Bool)
    (p : MvPolynomial σ ℂ) : assignmentHom vs bits p = assignmentValue vs bits p := by
  induction vs generalizing p with
  | nil => rfl
  | cons v vs ih => exact ih _ _

/-- Every sequential assignment is one simultaneous `aeval` substitution. -/
theorem assignmentValue_eq_aeval (vs : List σ) (bits : Fin vs.length → Bool)
    (p : MvPolynomial σ ℂ) :
    assignmentValue vs bits p = aeval (fun x => assignmentValue vs bits (X x)) p := by
  have he : assignmentHom vs bits = aeval (fun x => assignmentValue vs bits (X x)) := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [aeval_X,assignmentHom_apply]
  simpa only [assignmentHom_apply] using DFunLike.congr_fun he p

@[simp] theorem assignmentValue_C (vs : List σ) (bits : Fin vs.length → Bool) (c : ℂ) :
    assignmentValue vs bits (C c) = C c := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [assignmentValue, substitute_C]
    exact ih _

theorem assignmentValue_X_not_mem (vs : List σ) (bits : Fin vs.length → Bool)
    (x : σ) (hx : x ∉ vs) : assignmentValue vs bits (X x) = X x := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.mem_cons, not_or] at hx
    simp only [assignmentValue, substitute_X, if_neg hx.1]
    exact ih _ hx.2

theorem assignmentValue_X_get (vs : List σ) (bits : Fin vs.length → Bool)
    (h : vs.Nodup) (i : Fin vs.length) :
    assignmentValue vs bits (X (vs.get i)) = C (if bits i then 1 else 0) := by
  induction vs with
  | nil => exact Fin.elim0 i
  | cons v vs ih =>
    have hn := List.nodup_cons.mp h
    refine Fin.cases ?_ (fun j => ?_) i
    · change assignmentValue vs (fun k => bits k.succ)
          (substitute v (if bits 0 then 1 else 0) (X v)) = _
      rw [substitute_X]
      simp only [if_true]
      exact assignmentValue_C _ _ _
    · have hv : vs.get j ≠ v := by
        intro he
        apply hn.1
        rw [← he]
        exact List.get_mem vs j
      change assignmentValue vs (fun k => bits k.succ)
          (substitute v (if bits 0 then 1 else 0) (X (vs.get j))) = _
      simpa only [substitute_X, if_neg hv] using ih (fun k => bits k.succ) hn.2 j

/-- Simultaneous substitution maps every listed variable to its assigned bit
    and leaves every other variable unchanged. -/
noncomputable def simultaneousAssignment (vs : List σ) (bits : Fin vs.length → Bool)
    (x : σ) : MvPolynomial σ ℂ :=
  if hx : x ∈ vs then C (if bits ⟨vs.idxOf x, List.idxOf_lt_length_of_mem hx⟩ then 1 else 0)
  else X x

theorem assignmentValue_eq_simultaneous (vs : List σ) (bits : Fin vs.length → Bool)
    (h : vs.Nodup) (p : MvPolynomial σ ℂ) :
    assignmentValue vs bits p = aeval (simultaneousAssignment vs bits) p := by
  rw [assignmentValue_eq_aeval]
  have heq : (fun x => assignmentValue vs bits (X x)) = simultaneousAssignment vs bits := by
    funext x
    by_cases hx : x ∈ vs
    · simp only [simultaneousAssignment, dif_pos hx]
      have he := assignmentValue_X_get vs bits h ⟨vs.idxOf x, List.idxOf_lt_length_of_mem hx⟩
      simpa only [List.idxOf_get] using he
    · simp only [simultaneousAssignment, dif_neg hx]
      exact assignmentValue_X_not_mem vs bits x hx
  rw [heq]

/-- The iterated operation equals the sum over all Boolean assignments. -/
theorem booleanSum_eq_assignment_sum (vs : List σ) (p : MvPolynomial σ ℂ) :
    booleanSum vs p = ∑ bits : Fin vs.length → Bool, assignmentValue vs bits p := by
  induction vs generalizing p with
  | nil => simp [booleanSum,assignmentValue]
  | cons v vs ih =>
    change booleanSum vs (substitute v 0 p + substitute v 1 p) = _
    rw [booleanSum_add,ih,ih]
    have he := (Fin.consEquiv (fun _ : Fin (vs.length+1) => Bool)).sum_comp
      (fun bits => assignmentValue (v :: vs) bits p)
    refine (show _ = ∑ pair : Bool × (Fin vs.length → Bool),
      assignmentValue (v :: vs) ((Fin.consEquiv (fun _ : Fin (vs.length+1) => Bool)) pair) p from ?_).trans he
    simp only [Fintype.sum_prod_type]
    simp [assignmentValue,Fin.cons_zero,Fin.cons_succ,Fintype.sum_bool,add_comm]

/-- Boolean summation agrees with the usual sum of simultaneous evaluations. -/
theorem booleanSum_eq_simultaneous_sum (vs : List σ) (h : vs.Nodup)
    (p : MvPolynomial σ ℂ) :
    booleanSum vs p = ∑ bits : Fin vs.length → Bool,
      aeval (simultaneousAssignment vs bits) p := by
  rw [booleanSum_eq_assignment_sum]
  apply Finset.sum_congr rfl
  intro bits _
  exact assignmentValue_eq_simultaneous vs bits h p

/-- A sequence of selectors with at most two occurrences each can be eliminated
    with at most three new matrix dimensions per selector. -/
theorem eliminate_list (vs : List σ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (hM : IsSubstMatrix M)
    (hocc : ∀ v ∈ vs, (occurrences M v).card ≤ 2) :
    ∃ m ≤ n + 3*vs.length, ∃ N : Matrix (Fin m) (Fin m) (MvPolynomial σ ℂ),
      IsSubstMatrix N ∧ N.permanent = booleanSum vs M.permanent ∧
      (∀ v ∈ vs, occurrences N v = ∅) ∧
      ∀ w,(occurrences N w).card ≤ (occurrences M w).card := by
  induction vs generalizing n with
  | nil =>
    refine ⟨n,by simp,M,hM,rfl,?_,fun _ => le_rfl⟩
    simp
  | cons v vs ih =>
    have hv : (occurrences M v).card ≤ 2 := hocc v (by simp)
    obtain ⟨m,hm,N,hN,hval,hfree,hbound⟩ := eliminate_at_most_two M hM v hv
    have htail : ∀ w ∈ vs, (occurrences N w).card ≤ 2 := by
      intro w hw
      exact (hbound w).trans (hocc w (by simp [hw]))
    obtain ⟨k,hk,P,hP,hPval,hPfree,hPbound⟩ := ih N hN htail
    refine ⟨k,?_,P,hP,?_,?_,?_⟩
    · simp only [List.length_cons]
      omega
    · simpa only [booleanSum,← hval] using hPval
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · apply Finset.card_eq_zero.mp
        have hh := hPbound w
        rw [hfree] at hh
        simpa using hh
      · exact hPfree w hw
    · intro w
      exact (hPbound w).trans (hbound w)

/-- The iterated Boolean sum is a projection of a permanent whose dimension
    grows linearly in the number of eliminated selectors. -/
theorem booleanSum_isProjection (vs : List σ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (hM : IsSubstMatrix M)
    (hocc : ∀ v ∈ vs, (occurrences M v).card ≤ 2) :
    ∃ m ≤ n + 3*vs.length,
      IsProjection (booleanSum vs M.permanent) (genericMatrix m).permanent := by
  obtain ⟨m,hm,N,hN,hval,_,_⟩ := eliminate_list vs M hM hocc
  refine ⟨m,hm,?_⟩
  rw [← hval]
  exact hN.isProjection_permanent (Equiv.refl _)

/-- Summing a permanent over all simultaneous Boolean assignments preserves
    permanent projections when each selector appears in at most two entries. -/
theorem simultaneous_sum_isProjection (vs : List σ) (h : vs.Nodup) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (hM : IsSubstMatrix M)
    (hocc : ∀ v ∈ vs, (occurrences M v).card ≤ 2) :
    ∃ m ≤ n + 3*vs.length,
      IsProjection (∑ bits : Fin vs.length → Bool,
        aeval (simultaneousAssignment vs bits) M.permanent) (genericMatrix m).permanent := by
  rw [← booleanSum_eq_simultaneous_sum vs h M.permanent]
  exact booleanSum_isProjection vs M hM hocc

end PermanentSelectorIteration


-- BEGIN Solutions.PermanentEqualityCombine

namespace PermanentEqualityCombine

open MvPolynomial PermanentFoundation PermanentOccurrence PermanentSelectorIteration

variable {σ : Type} [DecidableEq σ]

/-- Equality polynomial for the variables in a list. -/
noncomputable def equalityPolynomial (vs : List σ) : MvPolynomial σ ℂ :=
  (∏ i : Fin vs.length, X (vs.get i)) + ∏ i : Fin vs.length, (1 - X (vs.get i))

theorem assignment_equalityPolynomial (vs : List σ) (h : vs.Nodup)
    (bits : Fin vs.length → Bool) :
    assignmentValue vs bits (equalityPolynomial vs) =
      (PermanentEqualitySelector.weight bits : MvPolynomial σ ℂ) := by
  have hx : ∀ i : Fin vs.length, assignmentHom vs bits (X (vs.get i)) =
      (if bits i then 1 else 0) := by
    intro i
    rw [assignmentHom_apply, assignmentValue_X_get vs bits h i]
    cases hb : bits i <;> simp [hb]
  rw [← assignmentHom_apply]
  simp only [equalityPolynomial, PermanentEqualitySelector.weight, map_add, map_prod, map_sub, map_one, hx]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases hb : bits i <;> simp [hb]

/-- The equality polynomial filters the Boolean sum down to the two constant
    assignments, even when the list is empty. -/
theorem booleanSum_equality (vs : List σ) (h : vs.Nodup) (p : MvPolynomial σ ℂ) :
    booleanSum vs (p * equalityPolynomial vs) =
      assignmentValue vs PermanentEqualitySelector.allTrue p +
      assignmentValue vs PermanentEqualitySelector.allFalse p := by
  rw [booleanSum_eq_assignment_sum]
  have he : ∀ bits : Fin vs.length → Bool,
      assignmentValue vs bits (p * equalityPolynomial vs) =
        PermanentEqualitySelector.weight bits * assignmentValue vs bits p := by
    intro bits
    rw [← assignmentHom_apply, map_mul, assignmentHom_apply, assignmentHom_apply,
      assignment_equalityPolynomial vs h bits, mul_comm]
  simp_rw [he]
  exact PermanentEqualitySelector.sum_weight (fun bits => assignmentValue vs bits p)

theorem equalityPolynomial_ofFn {m : ℕ} (v : Fin m → σ) :
    equalityPolynomial (List.ofFn v) =
      (∏ i, X (v i)) + ∏ i, (1 - X (v i)) := by
  unfold equalityPolynomial
  congr 1 <;>
    apply Fintype.prod_equiv (finCongr (List.length_ofFn (f := v))) <;>
    intro i <;> simp <;> congr 1 <;> apply Fin.ext <;> rfl

/-- A uniform assignment sets exactly the listed variables to the same bit. -/
theorem uniform_assignment_X (vs : List σ) (h : vs.Nodup) (b : Bool) (x : σ) :
    assignmentValue vs (fun _ => b) (X x) =
      if x ∈ vs then C (if b then 1 else 0) else X x := by
  by_cases hx : x ∈ vs
  · simp only [hx, if_true]
    have he := assignmentValue_X_get vs (fun _ => b) h
      ⟨vs.idxOf x, List.idxOf_lt_length_of_mem hx⟩
    simpa only [List.idxOf_get] using he
  · simp only [hx, if_false]
    exact assignmentValue_X_not_mem vs (fun _ => b) x hx

/-- Renaming split variables back to one variable commutes with their uniform
    Boolean evaluation, provided exactly those variables are merged. -/
theorem collapse_uniform_assignment {τ : Type} [DecidableEq τ]
    (vs : List σ) (h : vs.Nodup) (c : σ → τ) (u : τ)
    (hc : ∀ x, c x = u ↔ x ∈ vs) (b : Bool) (p : MvPolynomial σ ℂ) :
    aeval (fun x => (X (c x) : MvPolynomial τ ℂ))
        (assignmentValue vs (fun _ => b) p) =
      PermanentSelectorSubstitution.substitute u (if b then 1 else 0)
        (aeval (fun x => (X (c x) : MvPolynomial τ ℂ)) p) := by
  let ρ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ := aeval (fun x => X (c x))
  have he : ρ.comp (assignmentHom vs (fun _ => b)) =
      (PermanentSelectorSubstitution.substitute u (if b then 1 else 0)).comp ρ := by
    apply MvPolynomial.algHom_ext
    intro x
    simp only [AlgHom.comp_apply, assignmentHom_apply, uniform_assignment_X vs h b x,
      ρ, aeval_X, PermanentSelectorSubstitution.substitute_X]
    by_cases hx : x ∈ vs
    · have hu : c x = u := (hc x).2 hx
      simp [hx,hu]
    · have hu : c x ≠ u := fun he => hx ((hc x).1 he)
      simp [hx,hu]
  simpa only [AlgHom.comp_apply, assignmentHom_apply, ρ] using DFunLike.congr_fun he p

/-- After split variables are renamed back, equality filtering performs the
    original Boolean sum over the shared variable. -/
theorem collapse_booleanSum_equality {τ : Type} [DecidableEq τ]
    (vs : List σ) (h : vs.Nodup) (c : σ → τ) (u : τ)
    (hc : ∀ x, c x = u ↔ x ∈ vs) (p : MvPolynomial σ ℂ) :
    aeval (fun x => (X (c x) : MvPolynomial τ ℂ))
        (booleanSum vs (p * equalityPolynomial vs)) =
      PermanentSelectorSubstitution.substitute u 1
        (aeval (fun x => (X (c x) : MvPolynomial τ ℂ)) p) +
      PermanentSelectorSubstitution.substitute u 0
        (aeval (fun x => (X (c x) : MvPolynomial τ ℂ)) p) := by
  rw [booleanSum_equality vs h p, map_add]
  rw [show PermanentEqualitySelector.allTrue = (fun _ : Fin vs.length => true) from rfl,
      show PermanentEqualitySelector.allFalse = (fun _ : Fin vs.length => false) from rfl]
  simpa using congrArg₂ (· + ·)
    (collapse_uniform_assignment vs h c u hc true p)
    (collapse_uniform_assignment vs h c u hc false p)

/-- Occurrences in a block diagonal matrix are precisely the occurrences in
    its two diagonal blocks, embedded into the larger matrix. -/
theorem block_occurrences {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (A : Matrix α α (MvPolynomial σ ℂ)) (B : Matrix β β (MvPolynomial σ ℂ)) (v : σ) :
    occurrences (Matrix.fromBlocks A 0 0 B) v =
      (occurrences A v).image (fun p => (Sum.inl p.1, Sum.inl p.2)) ∪
      (occurrences B v).image (fun p => (Sum.inr p.1, Sum.inr p.2)) := by
  classical
  ext ⟨r,c⟩
  simp only [occurrences, Finset.mem_filter, Finset.mem_univ, true_and]
  cases r <;> cases c <;>
    simp [Matrix.fromBlocks, Ne.symm (MvPolynomial.X_ne_zero v)]

/-- Joining two permanent gadgets adds their variable occurrence counts. -/
theorem block_occurrences_card {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (A : Matrix α α (MvPolynomial σ ℂ)) (B : Matrix β β (MvPolynomial σ ℂ)) (v : σ) :
    (occurrences (Matrix.fromBlocks A 0 0 B) v).card =
      (occurrences A v).card + (occurrences B v).card := by
  classical
  rw [block_occurrences, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_iff.mpr, Finset.card_image_iff.mpr]
    · intro x _ y _ he; cases x; cases y; simp_all
    · intro x _ y _ he; cases x; cases y; simp_all
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨⟨a,b⟩,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨⟨c,d⟩,_,he⟩ := Finset.mem_image.mp hq
    cases he

/-- Multiply a read-once selector matrix by the equality gadget and eliminate
    all selector variables, with a linear bound on the resulting dimension. -/
theorem eliminate_with_equality {n m : ℕ} (A : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hA : IsSubstMatrix A) (v : Fin m → σ) (hv : Function.Injective v)
    (hocc : ∀ i, (occurrences A (v i)).card ≤ 1) :
    ∃ k ≤ n + (2 * m + 1) + 3 * m,
      ∃ N : Matrix (Fin k) (Fin k) (MvPolynomial σ ℂ), IsSubstMatrix N ∧
      N.permanent = PermanentSelectorIteration.booleanSum (List.ofFn v)
        (A.permanent * ((∏ i, X (v i)) + ∏ i, (1 - X (v i)))) ∧
      (∀ i, occurrences N (v i) = ∅) ∧
      (∀ w, (∀ i, v i ≠ w) → (occurrences N w).card ≤ (occurrences A w).card) := by
  obtain ⟨q,hq,B,hB,hBval,hBocc,hBfree⟩ := PermanentEqualityMatrix.equality_matrix_witness m v hv
  let e : Fin (n + q) ≃ Fin n ⊕ Fin q := finSumFinEquiv.symm
  let G := (Matrix.fromBlocks A 0 0 B).submatrix e e
  have hG : IsSubstMatrix G := (hA.fromBlocks .zero .zero hB).submatrix e e
  have hGval : G.permanent = A.permanent * ((∏ i, X (v i)) + ∏ i, (1 - X (v i))) := by
    change ((Matrix.fromBlocks A 0 0 B).submatrix e e).permanent = _
    rw [Matrix.permanent_submatrix_equiv, Matrix.permanent_fromBlocks_zero, hBval]
  have hGocc : ∀ w ∈ List.ofFn v, (occurrences G w).card ≤ 2 := by
    intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    change (occurrences ((Matrix.fromBlocks A 0 0 B).submatrix e e) (v i)).card ≤ 2
    rw [equiv_occurrences_card, block_occurrences_card]
    have ha := hocc i
    have hb := hBocc i
    omega
  obtain ⟨k,hk,N,hN,hval,hfree,hbound⟩ :=
    PermanentSelectorIteration.eliminate_list (List.ofFn v) G hG hGocc
  refine ⟨k, ?_, N, hN, ?_, ?_, ?_⟩
  · simp only [List.length_ofFn] at hk
    omega
  · simpa only [hGval] using hval
  · intro i
    exact hfree (v i) (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · intro w hw
    have hg : (occurrences G w).card = (occurrences A w).card := by
      change (occurrences ((Matrix.fromBlocks A 0 0 B).submatrix e e) w).card = _
      rw [equiv_occurrences_card, block_occurrences_card, hBfree w hw]
      simp
    exact (hbound w).trans_eq hg

/-- The sum of the two uniform substitutions in a read-once permanent is
    itself a polynomial-size permanent projection. -/
theorem uniform_substitutions_isProjection {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (hA : IsSubstMatrix A)
    (v : Fin m → σ) (hv : Function.Injective v)
    (hocc : ∀ i, (occurrences A (v i)).card ≤ 1) :
    ∃ k ≤ n + (2 * m + 1) + 3 * m,
      ResultantVNP.IsProjection
        (assignmentValue (List.ofFn v) PermanentEqualitySelector.allTrue A.permanent +
         assignmentValue (List.ofFn v) PermanentEqualitySelector.allFalse A.permanent)
        (genericMatrix k).permanent := by
  obtain ⟨k,hk,N,hN,hval,_,_⟩ := eliminate_with_equality A hA v hv hocc
  have he : booleanSum (List.ofFn v)
      (A.permanent * ((∏ i, X (v i)) + ∏ i, (1 - X (v i)))) =
      assignmentValue (List.ofFn v) PermanentEqualitySelector.allTrue A.permanent +
      assignmentValue (List.ofFn v) PermanentEqualitySelector.allFalse A.permanent := by
    rw [← equalityPolynomial_ofFn v]
    exact booleanSum_equality (List.ofFn v) (List.nodup_ofFn.mpr hv) A.permanent
  refine ⟨k,hk,?_⟩
  rw [← he, ← hval]
  exact hN.isProjection_permanent (Equiv.refl _)

/-- A Boolean sum over one variable is a small permanent projection when its
    occurrences have first been split into distinct read-once variables. -/
theorem split_then_sum_isProjection {τ : Type} [DecidableEq τ] {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (hA : IsSubstMatrix A)
    (v : Fin m → σ) (hv : Function.Injective v)
    (hocc : ∀ i, (occurrences A (v i)).card ≤ 1)
    (c : σ → τ) (u : τ) (hc : ∀ x, c x = u ↔ x ∈ List.ofFn v) :
    ∃ k ≤ n + (2 * m + 1) + 3 * m,
      ResultantVNP.IsProjection
        (PermanentSelectorSubstitution.substitute u 1
            (aeval (fun x => (X (c x) : MvPolynomial τ ℂ)) A.permanent) +
         PermanentSelectorSubstitution.substitute u 0
            (aeval (fun x => (X (c x) : MvPolynomial τ ℂ)) A.permanent))
        (genericMatrix k).permanent := by
  obtain ⟨k,hk,N,hN,hval,_,_⟩ := eliminate_with_equality A hA v hv hocc
  let ρ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ := aeval (fun x => X (c x))
  have hmapped : IsSubstMatrix (N.map ρ) := by
    intro i j
    obtain ⟨s,hs⟩ := hN i j
    cases s with
    | inl x =>
      have he : N i j = X x := hs.symm
      change IsSubstEntry (ρ (N i j))
      rw [he]
      simpa [ρ] using (IsSubstEntry.X (c x))
    | inr a =>
      have he : N i j = C a := hs.symm
      change IsSubstEntry (ρ (N i j))
      rw [he]
      simpa [ρ] using (IsSubstEntry.C a)
  have he : ρ N.permanent =
      PermanentSelectorSubstitution.substitute u 1 (ρ A.permanent) +
      PermanentSelectorSubstitution.substitute u 0 (ρ A.permanent) := by
    rw [hval, ← equalityPolynomial_ofFn v]
    exact collapse_booleanSum_equality (List.ofFn v) (List.nodup_ofFn.mpr hv) c u hc A.permanent
  refine ⟨k,hk,?_⟩
  change ResultantVNP.IsProjection
    (PermanentSelectorSubstitution.substitute u 1 (ρ A.permanent) +
      PermanentSelectorSubstitution.substitute u 0 (ρ A.permanent)) _
  rw [← he, AlgHom.map_permanent]
  exact hmapped.isProjection_permanent (Equiv.refl _)


end PermanentEqualityCombine

-- BEGIN Solutions.PermanentSplitVariables

namespace PermanentSplitVariables

open MvPolynomial PermanentFoundation PermanentOccurrence

variable {σ : Type} [DecidableEq σ] {n : ℕ}

/-- Positions in a substitution matrix whose entries are variables. -/
def VariablePosition (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) :=
  {p : Fin n × Fin n // ∃ x, M p.1 p.2 = X x}

noncomputable instance (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) :
    DecidableEq (VariablePosition M) := Classical.decEq _

noncomputable instance (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) :
    Fintype (VariablePosition M) := by
  classical
  unfold VariablePosition
  infer_instance

/-- The original variable appearing at a variable position. -/
noncomputable def originalVariable (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (p : VariablePosition M) : σ := Classical.choose p.property

theorem originalVariable_spec (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (p : VariablePosition M) : M p.1.1 p.1.2 = X (originalVariable M p) :=
  Classical.choose_spec p.property

theorem exists_constant (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (i j : Fin n) (h : ¬ ∃ x, M i j = X x) :
    ∃ c : ℂ, M i j = C c := by
  obtain ⟨s,hs⟩ := hM i j
  cases s with
  | inl x => exact (h ⟨x,hs.symm⟩).elim
  | inr c => exact ⟨c,hs.symm⟩

/-- Replace each variable occurrence by a different variable indexed by its
    matrix position, while leaving constants unchanged. -/
noncomputable def splitMatrix (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) : Matrix (Fin n) (Fin n) (MvPolynomial (VariablePosition M) ℂ) := by
  classical
  exact Matrix.of fun i j =>
    if h : ∃ x, M i j = X x then X ⟨(i,j),h⟩
    else C (Classical.choose (exists_constant M hM i j h))

theorem splitMatrix_isSubstMatrix (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) : IsSubstMatrix (splitMatrix M hM) := by
  classical
  intro i j
  simp only [splitMatrix, Matrix.of_apply]
  split_ifs
  · exact IsSubstEntry.X _
  · exact IsSubstEntry.C _

/-- Merging the fresh variables back into their original labels restores each
    entry of the original matrix. -/
theorem splitMatrix_merge_entry (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (i j : Fin n) :
    aeval (fun p => (X (originalVariable M p) : MvPolynomial σ ℂ))
      (splitMatrix M hM i j) = M i j := by
  classical
  simp only [splitMatrix, Matrix.of_apply]
  split_ifs with h
  · change (aeval (fun p : VariablePosition M => (X (originalVariable M p) : MvPolynomial σ ℂ)))
        (X (⟨(i,j),h⟩ : VariablePosition M)) = M i j
    exact (aeval_X (fun p : VariablePosition M => (X (originalVariable M p) : MvPolynomial σ ℂ))
      ⟨(i,j),h⟩).trans (originalVariable_spec M ⟨(i,j),h⟩).symm
  · rw [aeval_C]
    exact (Classical.choose_spec (exists_constant M hM i j h)).symm

theorem splitMatrix_merge_permanent (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) :
    aeval (fun p => (X (originalVariable M p) : MvPolynomial σ ℂ))
      (splitMatrix M hM).permanent = M.permanent := by
  rw [AlgHom.map_permanent]
  apply congrArg Matrix.permanent
  apply Matrix.ext
  intro i j
  exact splitMatrix_merge_entry M hM i j

/-- A fresh variable can appear only at the position from which it was made. -/
theorem splitMatrix_entry_position (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (p : VariablePosition M) (i j : Fin n)
    (h : splitMatrix M hM i j = X p) : (i,j) = p.val := by
  classical
  simp only [splitMatrix, Matrix.of_apply] at h
  split_ifs at h with hv
  · have he := MvPolynomial.X_injective h
    exact congrArg Subtype.val he
  · exact (constant_ne_variable _ p h).elim

theorem splitMatrix_occurrences_le_one (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : IsSubstMatrix M) (p : VariablePosition M) :
    (occurrences (splitMatrix M hM) p).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have ha' := splitMatrix_entry_position M hM p a.1 a.2 (Finset.mem_filter.mp ha).2
  have hb' := splitMatrix_entry_position M hM p b.1 b.2 (Finset.mem_filter.mp hb).2
  exact ha'.trans hb'.symm

/-- The Boolean sum over any one variable of an arbitrary substitution
    matrix is a permanent projection with a quadratic dimension bound. -/
theorem arbitrary_variable_sum_isProjection
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (hM : IsSubstMatrix M) (u : σ) :
    ∃ k ≤ n + (2 * (n * n) + 1) + 3 * (n * n),
      ResultantVNP.IsProjection
        (PermanentSelectorSubstitution.substitute u 1 M.permanent +
         PermanentSelectorSubstitution.substitute u 0 M.permanent)
        (genericMatrix k).permanent := by
  classical
  let S := {p : VariablePosition M // originalVariable M p = u}
  letI : Fintype S := by dsimp [S]; infer_instance
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let v : Fin (Fintype.card S) → VariablePosition M := fun i => (e i).val
  have hv : Function.Injective v := by
    intro i j he
    apply e.injective
    exact Subtype.ext he
  have hc : ∀ p : VariablePosition M, originalVariable M p = u ↔ p ∈ List.ofFn v := by
    intro p
    simp only [List.mem_ofFn]
    constructor
    · intro hp
      refine ⟨e.symm ⟨p,hp⟩, ?_⟩
      simp [v]
    · rintro ⟨i,hi⟩
      rw [← hi]
      exact (e i).property
  have hcard : Fintype.card S ≤ n * n := by
    have hi : Function.Injective (fun p : S => p.val.val) := by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      exact h
    have hh := Fintype.card_le_of_injective (fun p : S => p.val.val) hi
    simpa using hh
  obtain ⟨k,hk,hproj⟩ := PermanentEqualityCombine.split_then_sum_isProjection
    (splitMatrix M hM) (splitMatrix_isSubstMatrix M hM) v hv
    (fun i => splitMatrix_occurrences_le_one M hM (v i)) (originalVariable M) u hc
  rw [splitMatrix_merge_permanent M hM] at hproj
  refine ⟨k, ?_, hproj⟩
  omega


end PermanentSplitVariables

-- BEGIN Solutions.PermanentGroupElimination

namespace PermanentGroupElimination

open MvPolynomial PermanentFoundation PermanentOccurrence PermanentSelectorIteration
open PermanentEqualityCombine

variable {σ : Type} [DecidableEq σ]

/-- Evaluate all variables in one group at zero and at one, then add. -/
noncomputable def groupSum (vs : List σ) (p : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  assignmentValue vs PermanentEqualitySelector.allTrue p +
    assignmentValue vs PermanentEqualitySelector.allFalse p

/-- Perform the shared Boolean sums of all groups. -/
noncomputable def groupSums : List (List σ) → MvPolynomial σ ℂ → MvPolynomial σ ℂ
  | [], p => p
  | vs :: rest, p => groupSums rest (groupSum vs p)

def groupCost : List (List σ) → ℕ
  | [] => 0
  | vs :: rest => (2 * vs.length + 1) + 3 * vs.length + groupCost rest

theorem groupCost_eq (groups : List (List σ)) :
    groupCost groups = 5 * groups.flatten.length + groups.length := by
  induction groups with
  | nil => rfl
  | cons g rest ih => simp only [groupCost, List.flatten_cons, List.length_append,
      List.length_cons, ih]; omega

/-- The finite list of fresh variables that map to one original variable. -/
noncomputable def fibreList {α τ : Type} [Fintype α] [DecidableEq τ]
    (c : α → τ) (u : τ) : List α := by
  classical
  exact (Finset.univ.filter (fun x => c x = u)).toList

theorem mem_fibreList {α τ : Type} [Fintype α] [DecidableEq τ]
    (c : α → τ) (u : τ) (x : α) : x ∈ fibreList c u ↔ c x = u := by
  classical
  simp [fibreList]

theorem fibreList_nodup {α τ : Type} [Fintype α] [DecidableEq τ]
    (c : α → τ) (u : τ) : (fibreList c u).Nodup := by
  classical
  exact Finset.nodup_toList _

/-- Distinct original variables have disjoint lists of fresh copies. -/
theorem fibreLists_flatten_nodup {α τ : Type} [Fintype α] [DecidableEq τ]
    (c : α → τ) (us : List τ) (hu : us.Nodup) :
    (us.map (fibreList c)).flatten.Nodup := by
  classical
  induction us with
  | nil => simp
  | cons u rest ih =>
    obtain ⟨hu,hrest⟩ := List.nodup_cons.mp hu
    simp only [List.map_cons, List.flatten_cons]
    apply List.nodup_append'.mpr
    refine ⟨fibreList_nodup c u, ih hrest, ?_⟩
    apply List.disjoint_left.mpr
    intro x hx hxrest
    have hx' := (mem_fibreList c u x).mp hx
    obtain ⟨l,hl,hxl⟩ := List.mem_flatten.mp hxrest
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hl
    have hxw := (mem_fibreList c w x).mp hxl
    have : u = w := hx'.symm.trans hxw
    exact hu (this ▸ hw)

/-- The total cost of the fibre groups is linear in the number of fresh
    variables plus the number of original variables being summed. -/
theorem fibreGroups_cost_le {α τ : Type} [Fintype α] [DecidableEq τ]
    (c : α → τ) (us : List τ) (hu : us.Nodup) :
    groupCost (us.map (fibreList c)) ≤ 5 * Fintype.card α + us.length := by
  classical
  have hn := fibreLists_flatten_nodup c us hu
  have hc : (us.map (fibreList c)).flatten.length ≤ Fintype.card α := by
    calc
      _ = (us.map (fibreList c)).flatten.toFinset.card := (List.toFinset_card_of_nodup hn).symm
      _ ≤ Fintype.card α := Finset.card_le_univ _
  rw [groupCost_eq, List.length_map]
  omega

/-- Eliminate one read-once group while preserving all other occurrence bounds. -/
theorem eliminate_group {n : ℕ} (A : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hA : IsSubstMatrix A) (vs : List σ) (hv : vs.Nodup)
    (hocc : ∀ w ∈ vs, (occurrences A w).card ≤ 1) :
    ∃ k ≤ n + (2 * vs.length + 1) + 3 * vs.length,
      ∃ N : Matrix (Fin k) (Fin k) (MvPolynomial σ ℂ), IsSubstMatrix N ∧
      N.permanent = groupSum vs A.permanent ∧
      (∀ w, w ∉ vs → (occurrences N w).card ≤ (occurrences A w).card) := by
  obtain ⟨k,hk,N,hN,hval,_,hbound⟩ :=
    eliminate_with_equality A hA vs.get hv.injective_get (fun i => hocc _ (List.get_mem vs i))
  have hlist : List.ofFn vs.get = vs := by simp
  have hp : N.permanent = groupSum vs A.permanent := by
    rw [← equalityPolynomial_ofFn vs.get, hlist, booleanSum_equality vs hv] at hval
    exact hval
  refine ⟨k,hk,N,hN,hp,?_⟩
  intro w hw
  apply hbound w
  intro i he
  exact hw (he ▸ List.get_mem vs i)

/-- Disjoint read-once groups can all be eliminated with additive size cost. -/
theorem eliminate_groups (groups : List (List σ)) (hgroups : groups.flatten.Nodup)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hA : IsSubstMatrix A) (hocc : ∀ w ∈ groups.flatten, (occurrences A w).card ≤ 1) :
    ∃ k ≤ n + groupCost groups,
      ∃ N : Matrix (Fin k) (Fin k) (MvPolynomial σ ℂ),
        IsSubstMatrix N ∧ N.permanent = groupSums groups A.permanent := by
  induction groups generalizing n with
  | nil => exact ⟨n, by simp [groupCost], A, hA, rfl⟩
  | cons vs rest ih =>
    have hn : (vs ++ rest.flatten).Nodup := by simpa using hgroups
    obtain ⟨hvs,hrest,hdis⟩ := List.nodup_append'.mp hn
    have hfirst : ∀ w ∈ vs, (occurrences A w).card ≤ 1 := by
      intro w hw
      exact hocc w (by simp [hw])
    obtain ⟨k,hk,N,hN,hval,hbound⟩ := eliminate_group A hA vs hvs hfirst
    have htail : ∀ w ∈ rest.flatten, (occurrences N w).card ≤ 1 := by
      intro w hw
      have hnot : w ∉ vs := fun hin => List.disjoint_left.mp hdis hin hw
      exact (hbound w hnot).trans (hocc w (by simp [hw]))
    obtain ⟨q,hq,P,hP,hPval⟩ := ih hrest N hN htail
    refine ⟨q, ?_, P, hP, ?_⟩
    · simp only [groupCost] at *
      omega
    · simpa only [groupSums, ← hval] using hPval

/-- Merging a group after its shared sum is the same as summing the merged
    variable in the original polynomial. -/
theorem collapse_groupSum {τ : Type} [DecidableEq τ] (vs : List σ) (h : vs.Nodup)
    (c : σ → τ) (u : τ) (hc : ∀ x, c x = u ↔ x ∈ vs) (p : MvPolynomial σ ℂ) :
    aeval (fun x => (X (c x) : MvPolynomial τ ℂ)) (groupSum vs p) =
      PermanentSelectorSubstitution.substitute u 0
        (aeval (fun x => (X (c x) : MvPolynomial τ ℂ)) p) +
      PermanentSelectorSubstitution.substitute u 1
        (aeval (fun x => (X (c x) : MvPolynomial τ ℂ)) p) := by
  unfold groupSum
  rw [map_add]
  rw [show PermanentEqualitySelector.allTrue = (fun _ : Fin vs.length => true) from rfl,
      show PermanentEqualitySelector.allFalse = (fun _ : Fin vs.length => false) from rfl]
  have ht := collapse_uniform_assignment vs h c u hc true p
  have hf := collapse_uniform_assignment vs h c u hc false p
  simp only [Bool.false_eq_true, if_true, if_false] at ht hf
  rw [ht,hf,add_comm]

/-- Shared sums over fibres of a renaming become ordinary Boolean sums over
    their respective original variables. -/
theorem collapse_groupSums {τ : Type} [DecidableEq τ]
    (groups : List (τ × List σ)) (c : σ → τ)
    (hnodup : ∀ g ∈ groups, g.2.Nodup)
    (hfibre : ∀ g ∈ groups, ∀ x, c x = g.1 ↔ x ∈ g.2)
    (p : MvPolynomial σ ℂ) :
    aeval (fun x => (X (c x) : MvPolynomial τ ℂ))
      (groupSums (groups.map Prod.snd) p) =
    booleanSum (groups.map Prod.fst)
      (aeval (fun x => (X (c x) : MvPolynomial τ ℂ)) p) := by
  induction groups generalizing p with
  | nil => rfl
  | cons g rest ih =>
    have hn : ∀ z ∈ rest, z.2.Nodup := by
      intro z hz; exact hnodup z (by simp [hz])
    have hf : ∀ z ∈ rest, ∀ x, c x = z.1 ↔ x ∈ z.2 := by
      intro z hz; exact hfibre z (by simp [hz])
    simp only [List.map_cons, groupSums, booleanSum]
    rw [ih hn hf, collapse_groupSum g.2 (hnodup g (by simp)) c g.1
      (hfibre g (by simp)) p]

/-- Any collection of distinct Boolean sums of a permanent is a permanent
    projection, with a dimension quadratic in the input matrix size and linear
    in the number of summed variables. -/
theorem arbitrary_booleanSums_isProjection {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (hM : IsSubstMatrix M)
    (us : List σ) (hu : us.Nodup) :
    ∃ k ≤ n + 5 * (n * n) + us.length,
      ResultantVNP.IsProjection (booleanSum us M.permanent) (genericMatrix k).permanent := by
  classical
  let α := PermanentSplitVariables.VariablePosition M
  let c : α → σ := PermanentSplitVariables.originalVariable M
  let A := PermanentSplitVariables.splitMatrix M hM
  let groups := us.map (fibreList c)
  have hgroups : groups.flatten.Nodup := fibreLists_flatten_nodup c us hu
  have hA : IsSubstMatrix A := PermanentSplitVariables.splitMatrix_isSubstMatrix M hM
  have hocc : ∀ w ∈ groups.flatten, (occurrences A w).card ≤ 1 := by
    intro w _
    exact PermanentSplitVariables.splitMatrix_occurrences_le_one M hM w
  obtain ⟨k,hk,N,hN,hval⟩ := eliminate_groups groups hgroups A hA hocc
  have hcard : Fintype.card α ≤ n * n := by
    have hi : Function.Injective (fun p : α => p.val) := Subtype.val_injective
    have hc := Fintype.card_le_of_injective (fun p : α => p.val) hi
    simpa using hc
  have hcost : groupCost groups ≤ 5 * (n * n) + us.length := by
    have hc := fibreGroups_cost_le c us hu
    change groupCost (us.map (fibreList c)) ≤ _
    omega
  let ρ : MvPolynomial α ℂ →ₐ[ℂ] MvPolynomial σ ℂ := aeval (fun x => X (c x))
  have hmapped : IsSubstMatrix (N.map ρ) := by
    intro i j
    obtain ⟨s,hs⟩ := hN i j
    cases s with
    | inl x =>
      have he : N i j = X x := hs.symm
      change IsSubstEntry (ρ (N i j))
      rw [he]
      simpa [ρ] using (IsSubstEntry.X (c x))
    | inr a =>
      have he : N i j = C a := hs.symm
      change IsSubstEntry (ρ (N i j))
      rw [he]
      simpa [ρ] using (IsSubstEntry.C a)
  have hcollapse : ρ (groupSums groups A.permanent) = booleanSum us M.permanent := by
    let pairs := us.map (fun u => (u, fibreList c u))
    have hn : ∀ g ∈ pairs, g.2.Nodup := by
      intro g hg
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hg
      exact fibreList_nodup c u
    have hf : ∀ g ∈ pairs, ∀ x, c x = g.1 ↔ x ∈ g.2 := by
      intro g hg x
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hg
      exact (mem_fibreList c u x).symm
    have hc := collapse_groupSums pairs c hn hf A.permanent
    have hmerge : (aeval (fun x : α => (X (c x) : MvPolynomial σ ℂ))) A.permanent = M.permanent :=
      PermanentSplitVariables.splitMatrix_merge_permanent M hM
    simp only [pairs, List.map_map, Function.comp_def, List.map_id'] at hc
    rw [hmerge] at hc
    simpa only [groups, ρ] using hc
  have he : ρ N.permanent = booleanSum us M.permanent := by rw [hval, hcollapse]
  refine ⟨k, ?_, ?_⟩
  · omega
  · rw [← he, AlgHom.map_permanent]
    exact hmapped.isProjection_permanent (Equiv.refl _)


end PermanentGroupElimination

-- BEGIN Solutions.PermanentFormula
/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/



/- Adapted from cslib-frontier e78796a1e0c0fe124f9130a84850a5104bbe5f14,
CslibFrontier/Computability/Circuit/Arithmetic/Permanent/Formula.lean.
The final induction uses an explicit complex formula tree and the mission projection type. -/

namespace Matrix

open Equiv Equiv.Perm Finset Fintype

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {R : Type*} [CommSemiring R]

/-- Involution on `(Unit ⊕ m) ⊕ (Unit ⊕ n)` swapping the two root elements `inl (inl ())` and
`inr (inl ())`. -/
def swapRootEquiv (m n : Type*) :
    ((Unit ⊕ m) ⊕ (Unit ⊕ n)) ≃ ((Unit ⊕ m) ⊕ (Unit ⊕ n)) where
  toFun
    | .inl (.inl u) => .inr (.inl u)
    | .inl (.inr i) => .inl (.inr i)
    | .inr (.inl u) => .inl (.inl u)
    | .inr (.inr j) => .inr (.inr j)
  invFun
    | .inl (.inl u) => .inr (.inl u)
    | .inl (.inr i) => .inl (.inr i)
    | .inr (.inl u) => .inl (.inl u)
    | .inr (.inr j) => .inr (.inr j)
  left_inv x := by rcases x with (⟨⟨⟩⟩ | i) | (⟨⟨⟩⟩ | j) <;> rfl
  right_inv x := by rcases x with (⟨⟨⟩⟩ | i) | (⟨⟨⟩⟩ | j) <;> rfl

/-- Rooted permanent multiplication block matrix on `Unit ⊕ (m ⊕ (Unit ⊕ n))`. -/
def rootedMul (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R) (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R) :
    Matrix (Unit ⊕ (m ⊕ (Unit ⊕ n))) (Unit ⊕ (m ⊕ (Unit ⊕ n))) R :=
  (fromBlocks M₁ 0 (fromBlocks (1 : Matrix Unit Unit R) 0 0 0) M₂).submatrix
    (Equiv.sumAssoc Unit m (Unit ⊕ n)).symm
    ((Equiv.sumAssoc Unit m (Unit ⊕ n)).symm.trans (swapRootEquiv m n))

/-- The permanent of `rootedMul M₁ M₂` is the product of the permanents of `M₁` and `M₂`. -/
theorem permanent_rootedMul (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R)
    (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R) :
    (rootedMul M₁ M₂).permanent = M₁.permanent * M₂.permanent := by
  rw [rootedMul, permanent_submatrix_equiv_equiv, permanent_fromBlocks_zero₁₂]

/-- If the internal blocks of `M₁` and `M₂` have permanent `1`, then so does the internal block of
`rootedMul M₁ M₂`. -/
theorem permanent_toBlocks₂₂_rootedMul (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R)
    (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R)
    (h₁ : M₁.toBlocks₂₂.permanent = 1) (h₂ : M₂.toBlocks₂₂.permanent = 1) :
    (rootedMul M₁ M₂).toBlocks₂₂.permanent = 1 := by
  have hblk : (rootedMul M₁ M₂).toBlocks₂₂ =
      fromBlocks M₁.toBlocks₂₂ (of fun i => Sum.elim (M₁.toBlocks₂₁ i) 0) 0
        (fromBlocks (1 : Matrix Unit Unit R) M₂.toBlocks₁₂ 0 M₂.toBlocks₂₂) := by
    ext (i₁ | (⟨⟩ | i₂)) (j₁ | (⟨⟩ | j₂)) <;> rfl
  rw [hblk, permanent_fromBlocks_zero₂₁, permanent_fromBlocks_zero₂₁, permanent_one,
    h₁, h₂, mul_one, mul_one]

/-- Rooted permanent addition block matrix on `Unit ⊕ (m ⊕ (Unit ⊕ n))`. -/
def rootedAdd (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R) (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R) :
    Matrix (Unit ⊕ (m ⊕ (Unit ⊕ n))) (Unit ⊕ (m ⊕ (Unit ⊕ n))) R :=
  (fromBlocks
    M₁
    (fromBlocks M₂.toBlocks₁₁ M₂.toBlocks₁₂ 0 0)
    (fromBlocks (1 : Matrix Unit Unit R) 0 0 0)
    (fromBlocks (1 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂)).submatrix
    (Equiv.sumAssoc Unit m (Unit ⊕ n)).symm
    (Equiv.sumAssoc Unit m (Unit ⊕ n)).symm

/-- If the internal blocks of `M₁` and `M₂` have permanent `1`, then so does the internal block of
`rootedAdd M₁ M₂`. -/
theorem permanent_toBlocks₂₂_rootedAdd (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R)
    (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R)
    (h₁ : M₁.toBlocks₂₂.permanent = 1) (h₂ : M₂.toBlocks₂₂.permanent = 1) :
    (rootedAdd M₁ M₂).toBlocks₂₂.permanent = 1 := by
  have hblk : (rootedAdd M₁ M₂).toBlocks₂₂ =
      fromBlocks M₁.toBlocks₂₂ 0 0
        (fromBlocks (1 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂) := by
    ext (i₁ | (⟨⟩ | i₂)) (j₁ | (⟨⟩ | j₂)) <;> rfl
  rw [hblk, permanent_fromBlocks_zero, permanent_fromBlocks_zero₁₂, permanent_one,
    h₁, h₂, mul_one, mul_one]

/-- If the internal blocks of `M₁` and `M₂` have permanent `1`, then the permanent of
`rootedAdd M₁ M₂` is the sum of the permanents of `M₁` and `M₂`. -/
theorem permanent_rootedAdd (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R)
    (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R)
    (h₁ : M₁.toBlocks₂₂.permanent = 1) (h₂ : M₂.toBlocks₂₂.permanent = 1) :
    (rootedAdd M₁ M₂).permanent = M₁.permanent + M₂.permanent := by
  rw [rootedAdd, permanent_submatrix_equiv]
  let B₁ : Matrix ((Unit ⊕ m) ⊕ (Unit ⊕ n)) ((Unit ⊕ m) ⊕ (Unit ⊕ n)) R :=
    fromBlocks M₁ (fromBlocks M₂.toBlocks₁₁ M₂.toBlocks₁₂ 0 0) 0
      (fromBlocks (1 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂)
  let B₂ : Matrix ((Unit ⊕ m) ⊕ (Unit ⊕ n)) ((Unit ⊕ m) ⊕ (Unit ⊕ n)) R :=
    fromBlocks M₁ (fromBlocks M₂.toBlocks₁₁ M₂.toBlocks₁₂ 0 0)
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 0)
      (fromBlocks (0 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂)
  rw [permanent_add_of_row_eq _ B₁ B₂ (Sum.inr (Sum.inl ()))
    (fun j => by rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> simp [B₁, B₂])
    (fun i hi j => by
      rcases i with (⟨⟨⟩⟩ | i₁) | (⟨⟨⟩⟩ | i₂)
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl
      · exact (hi rfl).elim
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl)
    (fun i hi j => by
      rcases i with (⟨⟨⟩⟩ | i₁) | (⟨⟨⟩⟩ | i₂)
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl
      · exact (hi rfl).elim
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl)]
  have hB₁ : B₁.permanent = M₁.permanent := by
    rw [permanent_fromBlocks_zero₂₁, permanent_fromBlocks_zero₁₂, permanent_one, h₂, mul_one,
      mul_one]
  have hB₂_swap : B₂.submatrix (swapRootEquiv m n) (Equiv.refl _) =
      fromBlocks (fromBlocks (1 : Matrix Unit Unit R) 0 M₁.toBlocks₂₁ M₁.toBlocks₂₂) 0
        (fromBlocks M₁.toBlocks₁₁ M₁.toBlocks₁₂ 0 0) M₂ := by
    ext ((⟨⟨⟩⟩ | i₁) | (⟨⟨⟩⟩ | i₂)) ((⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂)) <;> rfl
  have hB₂ : B₂.permanent = M₂.permanent := by
    rw [← permanent_submatrix_equiv_equiv (swapRootEquiv m n) (Equiv.refl _), hB₂_swap,
      permanent_fromBlocks_zero₁₂, permanent_fromBlocks_zero₁₂, permanent_one, h₁, mul_one,
      one_mul]
  rw [hB₁, hB₂]

end Matrix

namespace PermanentFoundation

open MvPolynomial Finset ResultantVNP

universe u

variable {n m : ℕ} {σ : Type}

namespace IsSubstMatrix

theorem rootedMul {α β : Type*}
    {M₁ : Matrix (Unit ⊕ α) (Unit ⊕ α) (MvPolynomial σ ℂ)}
    {M₂ : Matrix (Unit ⊕ β) (Unit ⊕ β) (MvPolynomial σ ℂ)}
    (h₁ : IsSubstMatrix M₁) (h₂ : IsSubstMatrix M₂) :
    IsSubstMatrix (Matrix.rootedMul M₁ M₂) :=
  (h₁.fromBlocks .zero (IsSubstMatrix.one.fromBlocks .zero .zero .zero) h₂).submatrix _ _

theorem rootedAdd {α β : Type*}
    {M₁ : Matrix (Unit ⊕ α) (Unit ⊕ α) (MvPolynomial σ ℂ)}
    {M₂ : Matrix (Unit ⊕ β) (Unit ⊕ β) (MvPolynomial σ ℂ)}
    (h₁ : IsSubstMatrix M₁) (h₂ : IsSubstMatrix M₂) :
    IsSubstMatrix (Matrix.rootedAdd M₁ M₂) :=
  (h₁.fromBlocks (h₂.toBlocks₁₁.fromBlocks h₂.toBlocks₁₂ .zero .zero)
    (IsSubstMatrix.one.fromBlocks .zero .zero .zero)
    (IsSubstMatrix.one.fromBlocks .zero h₂.toBlocks₂₁ h₂.toBlocks₂₂)).submatrix _ _

end IsSubstMatrix

/-- A polynomial `P` has a *rooted permanent representation* of internal dimension `m` if it is
the permanent of a `(1 + m) × (1 + m)` specialization matrix `M` on `Unit ⊕ Fin m` whose internal
block `M.toBlocks₂₂` has permanent `1`. -/
def IsRootedPermProjection (m : ℕ) (P : MvPolynomial σ ℂ) : Prop :=
  ∃ M : Matrix (Unit ⊕ Fin m) (Unit ⊕ Fin m) (MvPolynomial σ ℂ),
    IsSubstMatrix M ∧ M.toBlocks₂₂.permanent = 1 ∧ M.permanent = P

namespace IsRootedPermProjection

/-- A rooted permanent representation of internal dimension `m` gives a projection of the
`(m + 1) × (m + 1)` generic permanent. -/
theorem to_isProjection_permanent {m : ℕ} {P : MvPolynomial σ ℂ}
    (h : IsRootedPermProjection m P) :
    IsProjection P (genericMatrix (m + 1)).permanent := by
  obtain ⟨M, hM, -, rfl⟩ := h
  have e : Fin (m + 1) ≃ Unit ⊕ Fin m :=
    (finCongr (Nat.add_comm m 1)).trans
      (finSumFinEquiv.symm.trans (Equiv.sumCongr finOneEquiv (Equiv.refl _)))
  exact hM.isProjection_permanent e

/-- Every single-entry substitution `P` (a variable or constant) has a rooted permanent
representation of internal dimension `0`. -/
theorem of_isSubstEntry {P : MvPolynomial σ ℂ} (hP : IsSubstEntry P) :
    IsRootedPermProjection 0 P := by
  refine ⟨Matrix.fromBlocks (Matrix.of fun _ _ => P) 0 0 0,
    IsSubstMatrix.fromBlocks (fun _ _ => hP) .zero .zero .zero,
    Matrix.permanent_isEmpty, ?_⟩
  rw [Matrix.permanent_fromBlocks_zero, Matrix.permanent_unique, Matrix.permanent_isEmpty, mul_one]
  rfl

/-- Every constant `C c` has a rooted permanent representation of internal dimension `0`. -/
theorem C (c : ℂ) : IsRootedPermProjection 0 (MvPolynomial.C c : MvPolynomial σ ℂ) :=
  .of_isSubstEntry (.C c)

/-- Every variable `X i` has a rooted permanent representation of internal dimension `0`. -/
theorem X (i : σ) : IsRootedPermProjection 0 (MvPolynomial.X i : MvPolynomial σ ℂ) :=
  .of_isSubstEntry (.X i)

/-- Equivalence `Fin (m₁ + 1 + m₂) ≃ Fin m₁ ⊕ (Unit ⊕ Fin m₂)` used to flatten internal blocks of
rooted permanent representations. -/
def innerEquiv (m₁ m₂ : ℕ) : Fin (m₁ + 1 + m₂) ≃ Fin m₁ ⊕ (Unit ⊕ Fin m₂) :=
  (finCongr (Nat.add_assoc m₁ 1 m₂)).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr (Equiv.refl _)
        (finSumFinEquiv.symm.trans (Equiv.sumCongr finOneEquiv (Equiv.refl _)))))

/-- Equivalence `Unit ⊕ Fin (m₁ + 1 + m₂) ≃ Unit ⊕ (Fin m₁ ⊕ (Unit ⊕ Fin m₂))`. -/
def outerEquiv (m₁ m₂ : ℕ) :
    Unit ⊕ Fin (m₁ + 1 + m₂) ≃ Unit ⊕ (Fin m₁ ⊕ (Unit ⊕ Fin m₂)) :=
  Equiv.sumCongr (Equiv.refl Unit) (innerEquiv m₁ m₂)

/-- **Additive closure of rooted permanent representations**: if `P` and `Q` have rooted permanent
representations of internal dimensions `m₁` and `m₂`, then `P + Q` has one of internal dimension
`m₁ + 1 + m₂`. -/
theorem add {m₁ m₂ : ℕ} {P Q : MvPolynomial σ ℂ}
    (hP : IsRootedPermProjection m₁ P) (hQ : IsRootedPermProjection m₂ Q) :
    IsRootedPermProjection (m₁ + 1 + m₂) (P + Q) := by
  obtain ⟨M₁, hM₁, hU₁, rfl⟩ := hP
  obtain ⟨M₂, hM₂, hU₂, rfl⟩ := hQ
  refine ⟨(Matrix.rootedAdd M₁ M₂).submatrix (outerEquiv m₁ m₂) (outerEquiv m₁ m₂),
    (hM₁.rootedAdd hM₂).submatrix _ _, ?_, ?_⟩
  · have hblk : ((Matrix.rootedAdd M₁ M₂).submatrix
        (outerEquiv m₁ m₂) (outerEquiv m₁ m₂)).toBlocks₂₂ =
        (Matrix.rootedAdd M₁ M₂).toBlocks₂₂.submatrix (innerEquiv m₁ m₂) (innerEquiv m₁ m₂) := rfl
    rw [hblk, Matrix.permanent_submatrix_equiv, Matrix.permanent_toBlocks₂₂_rootedAdd M₁ M₂ hU₁ hU₂]
  · rw [Matrix.permanent_submatrix_equiv, Matrix.permanent_rootedAdd M₁ M₂ hU₁ hU₂]

/-- **Multiplicative closure of rooted permanent representations**: if `P` and `Q` have rooted
permanent representations of internal dimensions `m₁` and `m₂`, then `P * Q` has one of internal
dimension `m₁ + 1 + m₂`. -/
theorem mul {m₁ m₂ : ℕ} {P Q : MvPolynomial σ ℂ}
    (hP : IsRootedPermProjection m₁ P) (hQ : IsRootedPermProjection m₂ Q) :
    IsRootedPermProjection (m₁ + 1 + m₂) (P * Q) := by
  obtain ⟨M₁, hM₁, hU₁, rfl⟩ := hP
  obtain ⟨M₂, hM₂, hU₂, rfl⟩ := hQ
  refine ⟨(Matrix.rootedMul M₁ M₂).submatrix (outerEquiv m₁ m₂) (outerEquiv m₁ m₂),
    (hM₁.rootedMul hM₂).submatrix _ _, ?_, ?_⟩
  · have hblk : ((Matrix.rootedMul M₁ M₂).submatrix
        (outerEquiv m₁ m₂) (outerEquiv m₁ m₂)).toBlocks₂₂ =
        (Matrix.rootedMul M₁ M₂).toBlocks₂₂.submatrix (innerEquiv m₁ m₂) (innerEquiv m₁ m₂) := rfl
    rw [hblk, Matrix.permanent_submatrix_equiv, Matrix.permanent_toBlocks₂₂_rootedMul M₁ M₂ hU₁ hU₂]
  · rw [Matrix.permanent_submatrix_equiv, Matrix.permanent_rootedMul M₁ M₂]

end IsRootedPermProjection


theorem Formula.rooted (F : Formula σ) : IsRootedPermProjection F.size F.value := by
  induction F with
  | var i => exact .X i
  | const c => exact .C c
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq

/-- Every formula is a projection of a permanent with one more row than its gate count. -/
theorem Formula.isProjection_permanent (F : Formula σ) :
    ResultantVNP.IsProjection F.value (genericMatrix (F.size+1)).permanent :=
  F.rooted.to_isProjection_permanent

end PermanentFoundation


-- BEGIN Solutions.PermanentFormulaBooleanSum

namespace PermanentFormulaBooleanSum

open MvPolynomial PermanentFoundation PermanentSelectorIteration PermanentGroupElimination

variable {σ τ : Type} [DecidableEq σ]

/-- A polynomial-size Boolean sum of a formula is a polynomial-size
    projection of a permanent. -/
theorem formula_booleanSum_isProjection (F : Formula σ) (vs : List σ) (hvs : vs.Nodup) :
    ∃ k ≤ (F.size + 1) + 5 * ((F.size + 1) * (F.size + 1)) + vs.length,
      ResultantVNP.IsProjection (booleanSum vs F.value) (genericMatrix k).permanent := by
  obtain ⟨M,hM,hval⟩ := isProjection_permanent_iff_exists_substMatrix.mp F.isProjection_permanent
  obtain ⟨k,hk,hproj⟩ := arbitrary_booleanSums_isProjection M hM vs hvs
  refine ⟨k,hk,?_⟩
  simpa only [hval] using hproj

/-- Renaming variables and specializing them to constants preserves the
    existence of a permanent projection, without increasing the dimension. -/
theorem projection_after_substitution {p : MvPolynomial σ ℂ} {k : ℕ}
    (ρ : σ → τ ⊕ ℂ) (hp : ResultantVNP.IsProjection p (genericMatrix k).permanent) :
    ResultantVNP.IsProjection (projection ρ p) (genericMatrix k).permanent := by
  obtain ⟨M,hM,hval⟩ := isProjection_permanent_iff_exists_substMatrix.mp hp
  have hmap : IsSubstMatrix (M.map (projection ρ)) := by
    intro i j
    obtain ⟨s,hs⟩ := hM i j
    cases s with
    | inl x =>
      have he : M i j = X x := hs.symm
      change IsSubstEntry (projection ρ (M i j))
      rw [he]
      cases hv : ρ x with
      | inl y => simpa [projection,hv] using (IsSubstEntry.X y)
      | inr c => simpa [projection,hv] using (IsSubstEntry.C c)
    | inr c =>
      have he : M i j = C c := hs.symm
      change IsSubstEntry (projection ρ (M i j))
      rw [he]
      simpa [projection] using (IsSubstEntry.C c)
  rw [← hval, AlgHom.map_permanent]
  exact hmap.isProjection_permanent (Equiv.refl _)

/-- Boolean summation followed by a projection is the sum of the corresponding
    simultaneous evaluations in the projected polynomial ring. -/
theorem project_booleanSum_eq_evaluations (p : MvPolynomial σ ℂ)
    (vs : List σ) (hvs : vs.Nodup) (ρ : σ → τ ⊕ ℂ) :
    projection ρ (booleanSum vs p) =
      ∑ bits : Fin vs.length → Bool,
        aeval (fun x => projection ρ (simultaneousAssignment vs bits x)) p := by
  rw [booleanSum_eq_simultaneous_sum vs hvs, map_sum]
  apply Finset.sum_congr rfl
  intro bits _
  exact MvPolynomial.comp_aeval_apply (f := simultaneousAssignment vs bits) (projection ρ) p

/-- On an original variable, a projected simultaneous assignment gives the
    assigned constant for a selector, and the projected entry otherwise. -/
theorem project_simultaneousAssignment (vs : List σ) (bits : Fin vs.length → Bool)
    (ρ : σ → τ ⊕ ℂ) (x : σ) :
    projection ρ (simultaneousAssignment vs bits x) =
      if hx : x ∈ vs then
        C (if bits ⟨vs.idxOf x, List.idxOf_lt_length_of_mem hx⟩ then 1 else 0)
      else Sum.elim X C (ρ x) := by
  classical
  by_cases hx : x ∈ vs
  · simp [simultaneousAssignment,projection,hx]
  · simp [simultaneousAssignment,projection,hx]

/-- The Boolean encoding agrees with the `Fin 2` constants used in VNP. -/
theorem finTwoEquiv_constant (z : Fin 2) :
    (if finTwoEquiv z then (1 : ℂ) else 0) = (z.val : ℂ) := by
  fin_cases z <;> norm_num [finTwoEquiv]

/-- Express the projected Boolean sum using the exact `Fin 2` assignment
    convention in the VNP definition. -/
theorem project_booleanSum_eq_finTwo (p : MvPolynomial σ ℂ)
    (vs : List σ) (hvs : vs.Nodup) (ρ : σ → τ ⊕ ℂ) :
    projection ρ (booleanSum vs p) =
      ∑ y : Fin vs.length → Fin 2,
        aeval (fun x => if hx : x ∈ vs then
          C (((y ⟨vs.idxOf x, List.idxOf_lt_length_of_mem hx⟩).val : ℂ))
          else Sum.elim X C (ρ x)) p := by
  classical
  rw [project_booleanSum_eq_evaluations p vs hvs ρ]
  let e : (Fin vs.length → Fin 2) ≃ (Fin vs.length → Bool) :=
    Equiv.piCongrRight (fun _ => finTwoEquiv)
  symm
  apply Fintype.sum_equiv e
  intro y
  have he : (fun x => if hx : x ∈ vs then
        C (((y ⟨vs.idxOf x, List.idxOf_lt_length_of_mem hx⟩).val : ℂ))
        else Sum.elim X C (ρ x)) =
      (fun x => projection ρ (simultaneousAssignment vs (e y) x)) := by
    funext x
    rw [project_simultaneousAssignment]
    by_cases hx : x ∈ vs
    · simp only [hx, dif_pos]
      congr 1
      exact (finTwoEquiv_constant _).symm
    · simp [hx]
  rw [he]

theorem formula_booleanSum_after_substitution (F : Formula σ) (vs : List σ) (hvs : vs.Nodup)
    (ρ : σ → τ ⊕ ℂ) :
    ∃ k ≤ (F.size + 1) + 5 * ((F.size + 1) * (F.size + 1)) + vs.length,
      ResultantVNP.IsProjection (projection ρ (booleanSum vs F.value)) (genericMatrix k).permanent := by
  obtain ⟨k,hk,hp⟩ := formula_booleanSum_isProjection F vs hvs
  exact ⟨k,hk,projection_after_substitution ρ hp⟩

private def PB (f : ℕ → ℕ) : Prop := ∃ a b : ℕ, ∀ n, f n ≤ a * (n+1)^b

private theorem pb_of_poly {f : ℕ → ℕ} (h : ResultantVNP.PolyBounded f) : PB f := by
  obtain ⟨c,hc⟩ := h
  refine ⟨2*c,c,fun n => (hc n).trans ?_⟩
  have hp : n^c ≤ (n+1)^c := Nat.pow_le_pow_left (by omega) c
  have hp1 : 1 ≤ (n+1)^c := Nat.one_le_pow c (n+1) (by omega)
  nlinarith

private theorem poly_of_pb {f : ℕ → ℕ} (h : PB f) : ResultantVNP.PolyBounded f := by
  obtain ⟨a,b,h⟩ := h
  let c := a * 2^b+b
  refine ⟨c,fun n => ?_⟩
  by_cases hn : n = 0
  · subst n
    have hh := h 0
    simp only [zero_add, one_pow, mul_one] at hh
    have hp : 1 ≤ 2^b := Nat.one_le_pow b 2 (by omega)
    have ha := Nat.mul_le_mul_left a hp
    simp only [mul_one] at ha
    dsimp [c]
    omega
  · have hn1 : 1 ≤ n := by omega
    have hp : (n+1)^b ≤ (2*n)^b := Nat.pow_le_pow_left (by omega) b
    rw [mul_pow] at hp
    have hbc : b ≤ c := by dsimp [c]; omega
    have hp' : n^b ≤ n^c := Nat.pow_le_pow_right hn1 hbc
    have ha : a*2^b ≤ c := by dsimp [c]; omega
    calc
      f n ≤ a*(n+1)^b := h n
      _ ≤ a*(2^b*n^b) := Nat.mul_le_mul_left a hp
      _ = (a*2^b)*n^b := by ring
      _ ≤ c*n^c := Nat.mul_le_mul ha hp'
      _ ≤ c*n^c+c := by omega

private theorem pb_const (c : ℕ) : PB (fun _ => c) := ⟨c,0,by simp⟩

private theorem pb_add {f g : ℕ → ℕ} (hf : PB f) (hg : PB g) :
    PB (fun n => f n + g n) := by
  obtain ⟨a,b,hf⟩ := hf
  obtain ⟨c,d,hg⟩ := hg
  refine ⟨a+c,b+d,fun n => ?_⟩
  have hb : (n+1)^b ≤ (n+1)^(b+d) := Nat.pow_le_pow_right (by omega) (by omega)
  have hd : (n+1)^d ≤ (n+1)^(b+d) := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    f n + g n ≤ a*(n+1)^b + c*(n+1)^d := Nat.add_le_add (hf n) (hg n)
    _ ≤ a*(n+1)^(b+d) + c*(n+1)^(b+d) :=
      Nat.add_le_add (Nat.mul_le_mul_left a hb) (Nat.mul_le_mul_left c hd)
    _ = (a+c)*(n+1)^(b+d) := by ring

private theorem pb_mul {f g : ℕ → ℕ} (hf : PB f) (hg : PB g) :
    PB (fun n => f n * g n) := by
  obtain ⟨a,b,hf⟩ := hf
  obtain ⟨c,d,hg⟩ := hg
  refine ⟨a*c,b+d,fun n => ?_⟩
  calc
    f n*g n ≤ (a*(n+1)^b)*(c*(n+1)^d) := Nat.mul_le_mul (hf n) (hg n)
    _ = (a*c)*(n+1)^(b+d) := by rw [pow_add]; ring

theorem polyBounded_add {f g : ℕ → ℕ} (hf : ResultantVNP.PolyBounded f)
    (hg : ResultantVNP.PolyBounded g) : ResultantVNP.PolyBounded (fun n => f n + g n) :=
  poly_of_pb (pb_add (pb_of_poly hf) (pb_of_poly hg))

/-- The permanent dimension bound is polynomial whenever the formula sizes
    and numbers of selectors are polynomially bounded. -/
theorem formula_dimension_polyBounded (s q : ℕ → ℕ)
    (hs : ResultantVNP.PolyBounded s) (hq : ResultantVNP.PolyBounded q) :
    ResultantVNP.PolyBounded (fun n => (s n + 1) + 5 * ((s n + 1) * (s n + 1)) + q n) := by
  have hb : PB (fun n => s n + 1) := pb_add (pb_of_poly hs) (pb_const 1)
  exact poly_of_pb (pb_add (pb_add hb (pb_mul (pb_const 5) (pb_mul hb hb))) (pb_of_poly hq))

/-- A family represented by polynomially bounded formula Boolean sums has
    a polynomially bounded family of permanent projections. -/
theorem formula_family_projection (f : ResultantVNP.PolyFamily) (d : ℕ → ℕ)
    (F : ∀ n, Formula (Fin (d n))) (vs : ∀ n, List (Fin (d n)))
    (ρ : ∀ n, Fin (d n) → Fin (f.nvars n) ⊕ ℂ)
    (hvs : ∀ n, (vs n).Nodup)
    (hf : ∀ n, f.p n = projection (ρ n) (booleanSum (vs n) (F n).value))
    (hbound : ResultantVNP.PolyBounded (fun n =>
      ((F n).size + 1) + 5 * (((F n).size + 1) * ((F n).size + 1)) + (vs n).length)) :
    ∃ t : ℕ → ℕ, ResultantVNP.PolyBounded t ∧ ∀ n,
      1 ≤ t n ∧ ResultantVNP.IsProjection (f.p n) (genericMatrix (t n)).permanent := by
  let B : ℕ → ℕ := fun n => ((F n).size + 1) +
    5 * (((F n).size + 1) * ((F n).size + 1)) + (vs n).length
  let t : ℕ → ℕ := fun n => max 1 (B n)
  have ht : ResultantVNP.PolyBounded t := by
    obtain ⟨c,hc⟩ := hbound
    by_cases hc0 : c = 0
    · subst c
      refine ⟨1, ?_⟩
      intro n
      have hn : B n = 0 := by have := hc n; simp only [zero_mul, add_zero] at this; omega
      simp [t,hn]
    · refine ⟨c, ?_⟩
      intro n
      apply max_le
      · have : 1 ≤ c := by omega
        omega
      · exact hc n
  refine ⟨t,ht,?_⟩
  intro n
  obtain ⟨k,hk,hp⟩ := formula_booleanSum_after_substitution (F n) (vs n) (hvs n) (ρ n)
  refine ⟨le_max_left _ _,?_⟩
  rw [hf n]
  exact isProjection_permanent_mono (hk.trans (le_max_right _ _)) hp

theorem formula_family_projection_of_bounds (f : ResultantVNP.PolyFamily) (d : ℕ → ℕ)
    (F : ∀ n, Formula (Fin (d n))) (vs : ∀ n, List (Fin (d n)))
    (ρ : ∀ n, Fin (d n) → Fin (f.nvars n) ⊕ ℂ)
    (hvs : ∀ n, (vs n).Nodup)
    (hf : ∀ n, f.p n = projection (ρ n) (booleanSum (vs n) (F n).value))
    (hs : ResultantVNP.PolyBounded (fun n => (F n).size))
    (hq : ResultantVNP.PolyBounded (fun n => (vs n).length)) :
    ∃ t : ℕ → ℕ, ResultantVNP.PolyBounded t ∧ ∀ n,
      1 ≤ t n ∧ ResultantVNP.IsProjection (f.p n) (genericMatrix (t n)).permanent :=
  formula_family_projection f d F vs ρ hvs hf
    (formula_dimension_polyBounded _ _ hs hq)


end PermanentFormulaBooleanSum

-- BEGIN Solutions.VNPAssignmentBridge

namespace VNPAssignmentBridge

open MvPolynomial PermanentFoundation PermanentSelectorIteration PermanentFormulaBooleanSum

/-- The VNP witness variables occupy the final `q` positions. -/
def witnessVariables (a q : ℕ) : List (Fin (a + q)) :=
  List.ofFn (Fin.natAdd a : Fin q → Fin (a + q))

/-- Retain the first `a` variables and project the witness variables to zero.
    The latter values are irrelevant after Boolean summation. -/
def outputProjection (a q : ℕ) : Fin (a + q) → Fin a ⊕ ℂ :=
  Fin.append (fun i => Sum.inl i) (fun _ => Sum.inr 0)

theorem witnessVariables_nodup (a q : ℕ) : (witnessVariables a q).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val h
  simp only [Fin.val_natAdd] at he
  omega

theorem witnessVariables_length (a q : ℕ) : (witnessVariables a q).length = q := by
  simp [witnessVariables]

theorem output_not_witness (a q : ℕ) (i : Fin a) :
    Fin.castAdd q i ∉ witnessVariables a q := by
  simp only [witnessVariables, List.mem_ofFn, not_exists]
  intro j he
  have he' := congrArg Fin.val he
  simp only [Fin.val_natAdd, Fin.val_castAdd] at he'
  have hi := i.isLt
  omega

theorem witness_mem (a q : ℕ) (j : Fin q) :
    Fin.natAdd a j ∈ witnessVariables a q := by
  exact List.mem_ofFn.mpr ⟨j,rfl⟩

/-- A canonical reindexing between the mission's witness coordinates and
    the positions in the selector list. -/
def selectorIndexEquiv (a q : ℕ) : Fin q ≃ Fin (witnessVariables a q).length :=
  (finCongr (witnessVariables_length a q)).symm

theorem witness_get (a q : ℕ) (j : Fin q) :
    (witnessVariables a q).get (selectorIndexEquiv a q j) = Fin.natAdd a j := by
  apply Fin.ext
  simp [witnessVariables, selectorIndexEquiv]
  rfl

def witnessAssignmentEquiv (a q : ℕ) :
    (Fin q → Fin 2) ≃ (Fin (witnessVariables a q).length → Bool) :=
  Equiv.arrowCongr (selectorIndexEquiv a q) finTwoEquiv

theorem witnessAssignmentEquiv_apply (a q : ℕ) (y : Fin q → Fin 2) (j : Fin q) :
    witnessAssignmentEquiv a q y (selectorIndexEquiv a q j) = finTwoEquiv (y j) := by
  simp [witnessAssignmentEquiv, Equiv.arrowCongr_apply]

/-- At each original variable position, evaluation leaves that variable in place. -/
theorem projected_assignment_output (a q : ℕ) (y : Fin q → Fin 2) (i : Fin a) :
    projection (outputProjection a q)
      (assignmentValue (witnessVariables a q) (witnessAssignmentEquiv a q y) (X (Fin.castAdd q i))) = X i := by
  rw [assignmentValue_X_not_mem _ _ _ (output_not_witness a q i)]
  simp [projection, outputProjection]

/-- At a witness position, evaluation gives the precise `Fin 2` constant. -/
theorem projected_assignment_witness (a q : ℕ) (y : Fin q → Fin 2) (j : Fin q) :
    projection (outputProjection a q)
      (assignmentValue (witnessVariables a q) (witnessAssignmentEquiv a q y) (X (Fin.natAdd a j))) =
        C (((y j).val : ℂ)) := by
  have hh := assignmentValue_X_get (witnessVariables a q) (witnessAssignmentEquiv a q y)
    (witnessVariables_nodup a q) (selectorIndexEquiv a q j)
  rw [witness_get, witnessAssignmentEquiv_apply, finTwoEquiv_constant] at hh
  rw [hh]
  simp [projection]

/-- The projected assignment agrees with the VNP definition on an entire
    polynomial, not just on its variable generators. -/
theorem projected_assignment_eq_vnp (a q : ℕ) (y : Fin q → Fin 2)
    (p : MvPolynomial (Fin (a + q)) ℂ) :
    projection (outputProjection a q)
      (assignmentValue (witnessVariables a q) (witnessAssignmentEquiv a q y) p) =
    aeval (Fin.append (fun i : Fin a => (X i : MvPolynomial (Fin a) ℂ))
      (fun j : Fin q => C (((y j).val : ℂ)))) p := by
  rw [assignmentValue_eq_aeval, MvPolynomial.comp_aeval_apply]
  have he : (fun x => projection (outputProjection a q)
      (assignmentValue (witnessVariables a q) (witnessAssignmentEquiv a q y) (X x))) =
      Fin.append (fun i : Fin a => (X i : MvPolynomial (Fin a) ℂ))
        (fun j : Fin q => C (((y j).val : ℂ))) := by
    funext x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) x
    · simpa only [Fin.append_left] using projected_assignment_output a q y i
    · simpa only [Fin.append_right] using projected_assignment_witness a q y j
  rw [he]

/-- The exact `Fin.append` / `Fin 2` Boolean sum used by VNP is the
    projected iterated Boolean sum used by the permanent construction. -/
theorem projected_booleanSum_eq_vnp (a q : ℕ) (p : MvPolynomial (Fin (a + q)) ℂ) :
    projection (outputProjection a q) (booleanSum (witnessVariables a q) p) =
      ∑ y : Fin q → Fin 2,
        aeval (Fin.append (fun i : Fin a => (X i : MvPolynomial (Fin a) ℂ))
          (fun j : Fin q => C (((y j).val : ℂ)))) p := by
  rw [booleanSum_eq_assignment_sum, map_sum]
  symm
  apply Fintype.sum_equiv (witnessAssignmentEquiv a q)
  intro y
  exact (projected_assignment_eq_vnp a q y p).symm

/-- The mission's Boolean sum of a formula is a permanent projection, with
    the input variables and witness variables in the exact VNP positions. -/
theorem vnp_formula_sum_isProjection (a q : ℕ) (F : Formula (Fin (a + q))) :
    ∃ k ≤ (F.size + 1) + 5 * ((F.size + 1) * (F.size + 1)) + q,
      ResultantVNP.IsProjection
        (∑ y : Fin q → Fin 2,
          aeval (Fin.append (fun i : Fin a => (X i : MvPolynomial (Fin a) ℂ))
            (fun j : Fin q => C (((y j).val : ℂ)))) F.value)
        (genericMatrix k).permanent := by
  obtain ⟨k,hk,hproj⟩ := formula_booleanSum_after_substitution F (witnessVariables a q)
    (witnessVariables_nodup a q) (outputProjection a q)
  rw [projected_booleanSum_eq_vnp] at hproj
  exact ⟨k, by simpa only [witnessVariables_length] using hk, hproj⟩

/-- A VNP-style family whose witness is computed by polynomial-size formulas
    has polynomial-size permanent projections in the exact mission convention. -/
theorem vnp_formula_family_isProjection (f : ResultantVNP.PolyFamily) (q : ℕ → ℕ)
    (F : ∀ n, Formula (Fin (f.nvars n + q n)))
    (hq : ResultantVNP.PolyBounded q)
    (hs : ResultantVNP.PolyBounded (fun n => (F n).size))
    (hf : ∀ n, f.p n = ∑ y : Fin (q n) → Fin 2,
      aeval (Fin.append (fun i : Fin (f.nvars n) => (X i : MvPolynomial (Fin (f.nvars n)) ℂ))
        (fun j : Fin (q n) => C (((y j).val : ℂ)))) (F n).value) :
    ∃ t : ℕ → ℕ, ResultantVNP.PolyBounded t ∧ ∀ n,
      1 ≤ t n ∧ ResultantVNP.IsProjection (f.p n) (genericMatrix (t n)).permanent := by
  apply formula_family_projection_of_bounds f (fun n => f.nvars n + q n) F
    (fun n => witnessVariables (f.nvars n) (q n))
    (fun n => outputProjection (f.nvars n) (q n))
    (fun n => witnessVariables_nodup (f.nvars n) (q n))
  · intro n
    rw [projected_booleanSum_eq_vnp]
    exact hf n
  · exact hs
  · simpa only [witnessVariables_length] using hq


end VNPAssignmentBridge

-- BEGIN Solutions.VNPNestedBooleanSum

namespace VNPNestedBooleanSum

open MvPolynomial PermanentFoundation

/-- Rename variables of a formula without changing its gate count. -/
def renameFormula {α β : Type} (f : α → β) : Formula α → Formula β
  | .var x => .var (f x)
  | .const a => .const a
  | .add p q => .add (renameFormula f p) (renameFormula f q)
  | .mul p q => .mul (renameFormula f p) (renameFormula f q)

theorem renameFormula_size {α β : Type} (f : α → β) (F : Formula α) :
    (renameFormula f F).size = F.size := by
  induction F <;> simp [renameFormula, Formula.size, *]

theorem renameFormula_value {α β : Type} (f : α → β) (F : Formula α) :
    (renameFormula f F).value = MvPolynomial.rename f F.value := by
  induction F <;> simp [renameFormula, Formula.value, *]

/-- Successive witness evaluations are the single evaluation obtained by
    concatenating their Boolean assignments. -/
theorem witnessEval_comp (a q r : ℕ) (y : Fin q → Fin 2) (z : Fin r → Fin 2)
    (p : MvPolynomial (Fin ((a + q) + r)) ℂ) :
    witnessEval a q y (witnessEval (a + q) r z p) =
      aeval (fun v : Fin ((a + q) + r) =>
        Fin.append (fun i : Fin a => (X i : MvPolynomial (Fin a) ℂ))
          (fun j : Fin (q + r) => C ((((Fin.append y z) j).val : ℂ)))
          (Fin.cast (Nat.add_assoc a q r) v)) p := by
  unfold witnessEval
  rw [MvPolynomial.comp_aeval_apply]
  have he : (fun v : Fin ((a + q) + r) =>
      (aeval (Fin.append (fun i : Fin a => (X i : MvPolynomial (Fin a) ℂ))
        (fun j : Fin q => C (((y j).val : ℂ)))))
        (Fin.append (fun i : Fin (a + q) => (X i : MvPolynomial (Fin (a + q)) ℂ))
          (fun j : Fin r => C (((z j).val : ℂ))) v)) =
      (fun v => Fin.append (fun i : Fin a => (X i : MvPolynomial (Fin a) ℂ))
        (fun j : Fin (q + r) => C ((((Fin.append y z) j).val : ℂ)))
        (Fin.cast (Nat.add_assoc a q r) v)) := by
    have hconst : Fin.append (fun j : Fin q => (C (((y j).val : ℂ)) : MvPolynomial (Fin a) ℂ))
        (fun j : Fin r => C (((z j).val : ℂ))) =
        (fun j : Fin (q + r) => C ((((Fin.append y z) j).val : ℂ))) := by
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
    rw [← hconst]
    change _ = (Fin.append (fun i : Fin a => (X i : MvPolynomial (Fin a) ℂ))
      (Fin.append (fun j : Fin q => C (((y j).val : ℂ)))
        (fun j : Fin r => C (((z j).val : ℂ)))) ∘ Fin.cast (Nat.add_assoc a q r))
    rw [← Fin.append_assoc]
    funext v
    refine Fin.addCases (fun i => ?_) (fun j => ?_) v
    · simp
    · simp
  rw [he]

/-- Two successive `Fin 2` sums combine into one sum over the concatenated
    witness vector. -/
theorem nested_witness_sums (a q r : ℕ) (p : MvPolynomial (Fin ((a + q) + r)) ℂ) :
    (∑ y : Fin q → Fin 2, witnessEval a q y
      (∑ z : Fin r → Fin 2, witnessEval (a + q) r z p)) =
    ∑ w : Fin (q + r) → Fin 2,
      aeval (fun v : Fin ((a + q) + r) =>
        Fin.append (fun i : Fin a => (X i : MvPolynomial (Fin a) ℂ))
          (fun j : Fin (q + r) => C (((w j).val : ℂ)))
          (Fin.cast (Nat.add_assoc a q r) v)) p := by
  classical
  simp only [map_sum]
  simp_rw [witnessEval_comp]
  calc
    _ = ∑ yz : (Fin q → Fin 2) × (Fin r → Fin 2),
        aeval (fun v : Fin ((a + q) + r) =>
          Fin.append (fun i : Fin a => (X i : MvPolynomial (Fin a) ℂ))
            (fun j : Fin (q + r) => C ((((Fin.append yz.1 yz.2) j).val : ℂ)))
            (Fin.cast (Nat.add_assoc a q r) v)) p := by
              rw [Fintype.sum_prod_type]
    _ = _ := by
      simpa only [Fin.appendEquiv_apply] using
        (Fin.appendEquiv (α := Fin 2) q r).sum_comp
          (fun w : Fin (q + r) → Fin 2 =>
            aeval (fun v : Fin ((a + q) + r) =>
              Fin.append (fun i : Fin a => (X i : MvPolynomial (Fin a) ℂ))
                (fun j : Fin (q + r) => C (((w j).val : ℂ)))
                (Fin.cast (Nat.add_assoc a q r) v)) p)

/-- A nested witness sum of a formula is a permanent projection with one
    polynomial-size bound depending on both witness lengths. -/
theorem nested_formula_sum_isProjection (a q r : ℕ) (F : Formula (Fin ((a + q) + r))) :
    ∃ k ≤ (F.size + 1) + 5 * ((F.size + 1) * (F.size + 1)) + (q + r),
      ResultantVNP.IsProjection
        (∑ y : Fin q → Fin 2, witnessEval a q y
          (∑ z : Fin r → Fin 2, witnessEval (a + q) r z F.value))
        (genericMatrix k).permanent := by
  let G := renameFormula (Fin.cast (Nat.add_assoc a q r)) F
  obtain ⟨k,hk,hproj⟩ := VNPAssignmentBridge.vnp_formula_sum_isProjection a (q+r) G
  refine ⟨k, ?_, ?_⟩
  · simpa only [G, renameFormula_size] using hk
  · rw [nested_witness_sums]
    simpa only [G, renameFormula_value, MvPolynomial.aeval_rename, Function.comp_def] using hproj

/-- A polynomial-size formula Boolean sum for a VP witness combines with the
    outer VNP Boolean sum and yields polynomial-size permanent projections. -/
theorem nested_formula_family_isProjection (f : ResultantVNP.PolyFamily) (q r : ℕ → ℕ)
    (F : ∀ n, Formula (Fin ((f.nvars n + q n) + r n)))
    (hq : ResultantVNP.PolyBounded q) (hr : ResultantVNP.PolyBounded r)
    (hs : ResultantVNP.PolyBounded (fun n => (F n).size))
    (hf : ∀ n, f.p n = ∑ y : Fin (q n) → Fin 2, witnessEval (f.nvars n) (q n) y
      (∑ z : Fin (r n) → Fin 2, witnessEval (f.nvars n + q n) (r n) z (F n).value)) :
    ∃ t : ℕ → ℕ, ResultantVNP.PolyBounded t ∧ ∀ n,
      1 ≤ t n ∧ ResultantVNP.IsProjection (f.p n) (genericMatrix (t n)).permanent := by
  let G : ∀ n, Formula (Fin (f.nvars n + (q n + r n))) :=
    fun n => renameFormula (Fin.cast (Nat.add_assoc (f.nvars n) (q n) (r n))) (F n)
  apply VNPAssignmentBridge.vnp_formula_family_isProjection f (fun n => q n + r n) G
    (PermanentFormulaBooleanSum.polyBounded_add hq hr)
  · simpa only [G, renameFormula_size] using hs
  · intro n
    rw [hf n, nested_witness_sums]
    simp only [G, renameFormula_value, MvPolynomial.aeval_rename, Function.comp_def]

/-- Renaming the retained variables commutes with evaluation of a trailing
    Boolean witness block, including the dependent index casts. -/
theorem witnessEval_cast (a b r : ℕ) (h : a = b) (z : Fin r → Fin 2)
    (p : MvPolynomial (Fin (a + r)) ℂ) :
    rename (Fin.cast h) (witnessEval a r z p) =
      witnessEval b r z (rename (Fin.cast (congrArg (fun t => t + r) h)) p) := by
  subst b
  simp [witnessEval]

/-- This isolates the only remaining complexity-theoretic bridge: once every
    VP family has a polynomial formula-sum representation, the mission's
    exact permanent hardness statement follows. -/
theorem permanent_hard_of_vp_formulaSums (hrep : VPFormulaSumProperty) :
    ResultantVNP.IsVNPHardPProj (fun n => (genericMatrix n).permanent) 1 := by
  intro f hf
  obtain ⟨g,hg,q,hq,houter⟩ := hf
  obtain ⟨r,hr,F,hs,hinner⟩ := hrep g hg
  choose hcast hsum using houter
  let H : ∀ n, Formula (Fin ((f.nvars n + q n) + r n)) :=
    fun n => renameFormula (Fin.cast (congrArg (fun t => t + r n) (hcast n))) (F n)
  have hHsize : ResultantVNP.PolyBounded (fun n => (H n).size) := by
    simpa only [H,renameFormula_size] using hs
  have hnest : ∀ n, f.p n = ∑ y : Fin (q n) → Fin 2, witnessEval (f.nvars n) (q n) y
      (∑ z : Fin (r n) → Fin 2, witnessEval (f.nvars n + q n) (r n) z (H n).value) := by
    intro n
    rw [hsum n]
    apply Finset.sum_congr rfl
    intro y _
    change aeval ((Fin.append (fun i : Fin (f.nvars n) => (X i : MvPolynomial (Fin (f.nvars n)) ℂ))
      (fun j : Fin (q n) => C (((y j).val : ℂ)))) ∘ Fin.cast (hcast n)) (g.p n) = _
    rw [← MvPolynomial.aeval_rename]
    change witnessEval (f.nvars n) (q n) y
      (rename (Fin.cast (hcast n)) (g.p n)) = _
    rw [hinner n, map_sum]
    apply congrArg (witnessEval (f.nvars n) (q n) y)
    apply Finset.sum_congr rfl
    intro z _
    rw [witnessEval_cast]
    simp only [H, renameFormula_value]
  exact nested_formula_family_isProjection f q r H hq hr hHsize hnest

/-- The conditional conclusion has the exact target type from Prove2Me. -/
theorem permanent_target_of_vp_formulaSums (hrep : VPFormulaSumProperty) :
    ResultantVNP.IsVNPHardPProj
      (fun n => (Matrix.of fun i j : Fin n =>
        (MvPolynomial.X (i,j) : MvPolynomial (Fin n × Fin n) ℂ)).permanent) 1 := by
  simpa only [genericMatrix] using permanent_hard_of_vp_formulaSums hrep



end VNPNestedBooleanSum

theorem solution : ResultantVNP.IsVNPHardPProj
  (fun n => (Matrix.of fun i j : Fin n =>
    (MvPolynomial.X (i,j) : MvPolynomial (Fin n × Fin n) ℂ)).permanent) 1 :=
  VNPNestedBooleanSum.permanent_target_of_vp_formulaSums ResultantVNP.vp_formula_sum

#print axioms solution
