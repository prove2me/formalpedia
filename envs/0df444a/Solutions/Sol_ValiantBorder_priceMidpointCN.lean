-- Prove2me | solution 1 for ValiantBorder.priceMidpointCN
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:08:03.586736+00:00
-- url     : https://prove2.me/submissions/037024eb-ea55-4798-895c-15289341b3a8

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_fieldCases

/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field*, sections “Tensors”,
“The metrics of the spectral points” and “Flat or contracting”, and Appendix N. Source:
`anthropics/formal-math` revision 11b6c7e3c927df2658f513b6b68ea7f8929c62c5, `vp-vnp/`, Apache-2.0. -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Determinants that factor, and the expansion of `det [[X, AΛB],[B'ΛA', Y]]`

Rows and columns fall into two groups. For every set `T` of inner indices the expansion has a term
`∏_T λ · α_T · β_T`, where `α_T` depends on `X, A, A'` and `β_T` on `Y, B, B'` only; it vanishes unless
`T` has as many elements on the left as on the right.
-/

namespace Nc.Cross

open Matrix Finset

section split

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

/-- The matrix with the entries of `N₁` in the rows and columns of the first group, those of `N₂` in the rows
and columns of the second, and zeros elsewhere. -/
def glueMat (rg cg : ι → Prop) [DecidablePred rg] [DecidablePred cg] (N₁ N₂ : Matrix ι ι R) :
    Matrix ι ι R :=
  of fun i j => if rg i then (if cg j then N₁ i j else 0) else (if cg j then 0 else N₂ i j)

theorem det_glue_zero_of_lt (rg cg : ι → Prop) [DecidablePred rg] [DecidablePred cg]
    (N₁ N₂ : Matrix ι ι R) (h : (univ.filter cg).card < (univ.filter rg).card) :
    (glueMat rg cg N₁ N₂).det = 0 := by
  rw [det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  obtain ⟨j, hj⟩ : ∃ j, rg (σ j) ∧ ¬ cg j := by
    by_contra hcon
    push Not at hcon
    refine absurd h (not_lt.2 ?_)
    refine Finset.card_le_card_of_injOn (fun i => σ.symm i) ?_ (fun i _ j _ hij => σ.symm.injective hij)
    intro i hi
    have hi' : rg i := (Finset.mem_filter.1 hi).2
    have := hcon (σ.symm i) (by simpa using hi')
    simpa using this
  have : ∏ i, glueMat rg cg N₁ N₂ (σ i) i = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) (by simp [glueMat, hj.1, hj.2])
  rw [this, smul_zero]

theorem det_glue_zero (rg cg : ι → Prop) [DecidablePred rg] [DecidablePred cg]
    (N₁ N₂ : Matrix ι ι R) (h : (univ.filter rg).card ≠ (univ.filter cg).card) :
    (glueMat rg cg N₁ N₂).det = 0 := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [← det_transpose]
    have : (glueMat rg cg N₁ N₂)ᵀ = glueMat cg rg N₁ᵀ N₂ᵀ := by
      ext i j
      by_cases h1 : cg i <;> by_cases h2 : rg j <;> simp [glueMat, h1, h2]
    rw [this]
    exact det_glue_zero_of_lt cg rg _ _ h
  · exact det_glue_zero_of_lt rg cg _ _ h

/-- A glued determinant is a product. -/
theorem det_glue (rg cg : ι → Prop) [DecidablePred rg] [DecidablePred cg] :
    ∃ (α β : Matrix ι ι R → R), ∀ N₁ N₂, (glueMat rg cg N₁ N₂).det = α N₁ * β N₂ := by
  by_cases h : (univ.filter rg).card = (univ.filter cg).card
  swap
  · exact ⟨fun _ => 0, fun _ => 0, fun N₁ N₂ => by rw [det_glue_zero _ _ _ _ h, zero_mul]⟩
  have hc : Fintype.card {i // cg i} = Fintype.card {i // rg i} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, h]
  let e : {i // cg i} ≃ {i // rg i} := Fintype.equivOfCardEq hc
  let τ : Equiv.Perm ι := Equiv.extendSubtype e
  have h1 : ∀ i, cg i → rg (τ i) := fun i hi => Equiv.extendSubtype_mem e i hi
  have h2 : ∀ i, ¬ cg i → ¬ rg (τ i) := fun i hi => Equiv.extendSubtype_not_mem e i hi
  refine ⟨fun N₁ => ((Equiv.Perm.sign τ : ℤ) : R) * (toSquareBlockProp (N₁.submatrix τ id) cg).det,
    fun N₂ => (toSquareBlockProp (N₂.submatrix τ id) fun i => ¬ cg i).det, fun N₁ N₂ => ?_⟩
  have hp := det_permute τ (glueMat rg cg N₁ N₂)
  have hs : ((Equiv.Perm.sign τ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) = 1 := by
    rw [← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]
  have hb : ((glueMat rg cg N₁ N₂).submatrix τ id).det =
      (toSquareBlockProp (N₁.submatrix τ id) cg).det *
        (toSquareBlockProp (N₂.submatrix τ id) fun i => ¬ cg i).det := by
    rw [twoBlockTriangular_det _ cg]
    · congr 1
      · congr 1
        ext i j
        simp [toSquareBlockProp, glueMat, h1 i i.2, j.2]
      · congr 1
        ext i j
        simp [toSquareBlockProp, glueMat, h2 i i.2, j.2]
    · intro i hi j hj
      simp [glueMat, h2 i hi, hj]
  rw [hb] at hp
  linear_combination (-(glueMat rg cg N₁ N₂).det) * hs - ((Equiv.Perm.sign τ : ℤ) : R) * hp

end split

section expand

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] {R : Type*} [CommRing R]

/-- Expansion of a determinant in the rows `λ_r v_r + e_r`. -/
theorem det_expand (P : n → (n ⊕ m) → R) (l : m → R) (v e : m → (n ⊕ m) → R) :
    (of (Sum.elim P (fun r => l r • v r + e r)) : Matrix (n ⊕ m) (n ⊕ m) R).det =
      ∑ T : Finset m, (∏ r ∈ T, l r) *
        (of (Sum.elim P (T.piecewise v e)) : Matrix (n ⊕ m) (n ⊕ m) R).det := by
  let g : MultilinearMap R (fun _ : m => (n ⊕ m) → R) R :=
    (MultilinearMap.currySum (detRowAlternating (n := n ⊕ m) (R := R)).toMultilinearMap) P
  have hg : ∀ w : m → (n ⊕ m) → R, g w = (of (Sum.elim P w) : Matrix (n ⊕ m) (n ⊕ m) R).det := by
    intro w
    rfl
  have h1 := g.map_add_univ (fun r => l r • v r) e
  have h2 : ∀ T : Finset m, g (T.piecewise (fun r => l r • v r) e) =
      (∏ r ∈ T, l r) * g (T.piecewise v e) := by
    intro T
    have := g.map_piecewise_smul l (T.piecewise v e) T
    rw [smul_eq_mul] at this
    rw [← this]
    congr 1
    ext r : 1
    by_cases hr : r ∈ T <;> simp [hr]
  calc (of (Sum.elim P (fun r => l r • v r + e r)) : Matrix (n ⊕ m) (n ⊕ m) R).det
      = g ((fun r => l r • v r) + e) := rfl
    _ = ∑ T : Finset m, g (T.piecewise (fun r => l r • v r) e) := h1
    _ = _ := Finset.sum_congr rfl fun T _ => by rw [h2, hg]

end expand

end Nc.Cross
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# States, and the terms of the expansion of `det [[X, AΛB],[B'ΛA', Y]]`

The definitions for the step "The coefficients" of the proof of Proposition prop:identity; the step itself is in
Paper/Identity.lean (Paper.prop_identity_schur to Paper.prop_identity_near). In the paper's letters `X = M₁`, `Y = M₂`, `A = F`,
`A' = F′`, `B = G`, `B' = −G′` and `Λ = D`.
-/

set_option linter.unusedSectionVars false

namespace Nc.Cross

open Matrix Finset

/-- The energy `∑ (2i+1)` of a set. -/
def en (S : Finset ℕ) : ℕ := ∑ i ∈ S, (2 * i + 1)

/-- The states of energy at most `E`. -/
def pairs (E : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((range E).powerset ×ˢ (range E).powerset).filter
    fun s => s.1.card = s.2.card ∧ en s.1 + en s.2 ≤ E

theorem lt_of_mem_en {S : Finset ℕ} {E i : ℕ} (h : en S ≤ E) (hi : i ∈ S) : i < E := by
  have : 2 * i + 1 ≤ en S := Finset.single_le_sum (f := fun i => 2 * i + 1) (fun _ _ => Nat.zero_le _) hi
  omega

theorem mem_pairs {E : ℕ} {s : Finset ℕ × Finset ℕ} :
    s ∈ pairs E ↔ s.1.card = s.2.card ∧ en s.1 + en s.2 ≤ E := by
  unfold pairs
  rw [mem_filter, mem_product, mem_powerset, mem_powerset]
  refine ⟨fun h => h.2, fun h => ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, h⟩⟩
  · exact mem_range.2 (lt_of_mem_en (by omega) hi)
  · exact mem_range.2 (lt_of_mem_en (by omega) hi)

section

variable {p q ρ : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q] [Fintype ρ] [DecidableEq ρ]
variable {R : Type*} [CommRing R]

/-- The upper rows `(X, 0, A, 0)` and `(0, Y, 0, B')` of the big matrix. -/
def topRows (X : Matrix p p R) (A : Matrix p ρ R) (Y : Matrix q q R) (B' : Matrix q ρ R) :
    p ⊕ q → (p ⊕ q) ⊕ (ρ ⊕ ρ) → R :=
  fun i => Sum.elim (fromBlocks X 0 0 Y i) (fromBlocks A 0 0 B' i)

/-- The parts `(0, −B, 0, 0)` and `(−A', 0, 0, 0)` of the lower rows, without the factors from `Λ`. -/
def lowRows (A' : Matrix ρ p R) (B : Matrix ρ q R) : ρ ⊕ ρ → (p ⊕ q) ⊕ (ρ ⊕ ρ) → R :=
  fun r => Sum.elim (-(fromBlocks 0 B A' 0 : Matrix (ρ ⊕ ρ) (p ⊕ q) R) r) 0

/-- The parts of the lower rows with the entry 1. -/
def unitRows : ρ ⊕ ρ → (p ⊕ q) ⊕ (ρ ⊕ ρ) → R :=
  fun r => Sum.elim 0 ((1 : Matrix (ρ ⊕ ρ) (ρ ⊕ ρ) R) r)

/-- The matrix of the term of `T`: in the lower rows in `T` the first part is taken, in the others the entry 1. -/
def termMat (T : Finset (ρ ⊕ ρ)) (X : Matrix p p R) (A : Matrix p ρ R) (A' : Matrix ρ p R)
    (Y : Matrix q q R) (B : Matrix ρ q R) (B' : Matrix q ρ R) :
    Matrix ((p ⊕ q) ⊕ (ρ ⊕ ρ)) ((p ⊕ q) ⊕ (ρ ⊕ ρ)) R :=
  of (Sum.elim (topRows X A Y B') (T.piecewise (lowRows A' B) unitRows))

/-- Columns of the first group. -/
def cgrp : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop
  | Sum.inl (Sum.inl _) => True
  | Sum.inl (Sum.inr _) => False
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr _) => False

/-- Rows of the first group. -/
def rgrp (T : Finset (ρ ⊕ ρ)) : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop
  | Sum.inl (Sum.inl _) => True
  | Sum.inl (Sum.inr _) => False
  | Sum.inr (Sum.inl r) => Sum.inl r ∉ T
  | Sum.inr (Sum.inr r) => Sum.inr r ∈ T

instance : DecidablePred (cgrp : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop) := fun i =>
  match i with
  | Sum.inl (Sum.inl _) => isTrue trivial
  | Sum.inl (Sum.inr _) => isFalse id
  | Sum.inr (Sum.inl _) => isTrue trivial
  | Sum.inr (Sum.inr _) => isFalse id

instance (T : Finset (ρ ⊕ ρ)) : DecidablePred (rgrp T : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop) := fun i =>
  match i with
  | Sum.inl (Sum.inl _) => isTrue trivial
  | Sum.inl (Sum.inr _) => isFalse id
  | Sum.inr (Sum.inl r) => inferInstanceAs (Decidable (Sum.inl r ∉ T))
  | Sum.inr (Sum.inr r) => inferInstanceAs (Decidable (Sum.inr r ∈ T))

/-- The matrix of a term falls into two blocks: one made of `X, A, A'` and one made of `Y, B, B'`. -/
theorem termMat_eq_glue (T : Finset (ρ ⊕ ρ)) (X : Matrix p p R) (A : Matrix p ρ R) (A' : Matrix ρ p R)
    (Y : Matrix q q R) (B : Matrix ρ q R) (B' : Matrix q ρ R) :
    termMat T X A A' Y B B' =
      glueMat (rgrp T) cgrp (termMat T X A A' 0 0 0) (termMat T 0 0 0 Y B B') := by
  ext i j
  rcases i with (i | i) | (i | i)
  · rcases j with (j | j) | (j | j) <;> simp [termMat, glueMat, rgrp, cgrp, topRows]
  · rcases j with (j | j) | (j | j) <;> simp [termMat, glueMat, rgrp, cgrp, topRows]
  · by_cases hi : Sum.inl i ∈ T <;> rcases j with (j | j) | (j | j) <;>
      simp [termMat, glueMat, rgrp, cgrp, lowRows, unitRows, hi]
  · by_cases hi : Sum.inr i ∈ T <;> rcases j with (j | j) | (j | j) <;>
      simp [termMat, glueMat, rgrp, cgrp, lowRows, unitRows, hi]

theorem card_cgrp : (univ.filter (cgrp : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop)).card =
    Fintype.card p + Fintype.card ρ := by
  have h : univ.filter (cgrp : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop) =
      disjSum (disjSum univ ∅) (disjSum univ ∅) := by
    ext i
    rcases i with (i | i) | (i | i) <;> simp [cgrp]
  rw [h]
  simp [Finset.card_univ]

theorem card_rgrp (T : Finset (ρ ⊕ ρ)) :
    (univ.filter (rgrp T : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop)).card + T.toLeft.card =
    Fintype.card p + Fintype.card ρ + T.toRight.card := by
  have h : univ.filter (rgrp T : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop) =
      disjSum (disjSum univ ∅) (disjSum T.toLeftᶜ T.toRight) := by
    ext i
    rcases i with (i | i) | (i | i) <;> simp [rgrp]
  rw [h]
  have := Finset.card_add_card_compl T.toLeft
  simp only [card_disjSum, Finset.card_univ, card_empty]
  omega

end

section coeff

open Polynomial

/-- The paper's `E(T)`, for `T = (T₁, T₂)`. -/
def enT {K : ℕ} (T : Finset (Fin K ⊕ Fin K)) : ℕ :=
  ∑ r ∈ T, Sum.elim (fun r : Fin K => 2 * (r : ℕ) + 1) (fun r : Fin K => 2 * (r : ℕ) + 1) r

/-- The `T` with `|T₁| = |T₂|` and `E(T) ≤ N`: the terms that contribute to the coefficient of `x^N`. -/
def goodT (K N : ℕ) : Finset (Finset (Fin K ⊕ Fin K)) :=
  univ.filter fun T => T.toLeft.card = T.toRight.card ∧ enT T ≤ N

end coeff

end Nc.Cross
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The number of states: lemmas

Lemmas for Paper.lem_count (Paper/States.lean): gluing `k` sets along the residues modulo `k`, and the sets of bounded
energy.
-/

namespace Nc.Cross

open Finset

/-- Glue `k` sets along the residues modulo `k`. -/
def glueSet (k : ℕ) (I : Fin k → Finset ℕ) : Finset ℕ :=
  univ.biUnion fun r => (I r).image fun i => k * i + r

theorem mem_glueSet {k : ℕ} (I : Fin k → Finset ℕ) (r : Fin k) (i : ℕ) :
    k * i + r ∈ glueSet k I ↔ i ∈ I r := by
  have hk : 0 < k := r.pos
  unfold glueSet
  simp only [mem_biUnion, mem_univ, true_and, mem_image]
  refine ⟨?_, fun h => ⟨r, i, h, rfl⟩⟩
  rintro ⟨r', i', hi', h⟩
  have h1 : (r' : ℕ) = r := by
    have := congrArg (· % k) h
    simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt r.2, Nat.mod_eq_of_lt r'.2] using this
  have h2 : r' = r := Fin.ext h1
  subst h2
  have h3 : i' = i := Nat.eq_of_mul_eq_mul_left hk (by omega)
  exact h3 ▸ hi'

theorem glueSet_injective {k : ℕ} : Function.Injective (glueSet k) := by
  intro I I' h
  funext r
  ext i
  rw [← mem_glueSet I r i, h, mem_glueSet]

theorem sum_glueSet {k : ℕ} (I : Fin k → Finset ℕ) (f : ℕ → ℕ) :
    ∑ n ∈ glueSet k I, f n = ∑ r, ∑ i ∈ I r, f (k * i + r) := by
  unfold glueSet
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact Nat.eq_of_mul_eq_mul_left r.pos (by simpa using hij)
  · intro r _ r' _ hrr'
    rw [Function.onFun, Finset.disjoint_left]
    intro n hn hn'
    obtain ⟨i, -, rfl⟩ := mem_image.1 hn
    obtain ⟨i', -, h⟩ := mem_image.1 hn'
    apply hrr'
    have := congrArg (· % k) h
    refine Fin.ext ?_
    simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt r.2, Nat.mod_eq_of_lt r'.2] using this.symm

theorem card_glueSet {k : ℕ} (I : Fin k → Finset ℕ) : (glueSet k I).card = ∑ r, (I r).card := by
  have := sum_glueSet I fun _ => 1
  simpa using this

theorem en_glueSet {k : ℕ} (s : Fin k → Finset ℕ × Finset ℕ) (h : ∀ r, (s r).1.card = (s r).2.card) :
    en (glueSet k fun r => (s r).1) + en (glueSet k fun r => (s r.rev).2) =
      k * ∑ r, (en (s r).1 + en (s r).2) := by
  have e1 : en (glueSet k fun r => (s r.rev).2) = ∑ r : Fin k, ∑ i ∈ (s r).2, (2 * (k * i + (r.rev : Fin k)) + 1) := by
    rw [en, sum_glueSet]
    refine Fintype.sum_equiv Fin.revPerm _ _ fun r => ?_
    simp
  rw [e1, en, sum_glueSet, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr : ((r.rev : Fin k) : ℕ) + r + 1 = k := by
    rw [Fin.val_rev]
    omega
  have a1 : ∑ i ∈ (s r).1, (2 * (k * i + r) + 1) = k * ∑ i ∈ (s r).1, 2 * i + (s r).1.card * (2 * r + 1) := by
    rw [Finset.mul_sum, Finset.card_eq_sum_ones, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have a2 : ∑ i ∈ (s r).2, (2 * (k * i + (r.rev : Fin k)) + 1) =
      k * ∑ i ∈ (s r).2, 2 * i + (s r).2.card * (2 * (r.rev : Fin k) + 1) := by
    rw [Finset.mul_sum, Finset.card_eq_sum_ones, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have a3 : ∀ S : Finset ℕ, en S = ∑ i ∈ S, 2 * i + S.card := by
    intro S
    rw [en, Finset.sum_add_distrib, Finset.card_eq_sum_ones]
  rw [a1, a2, a3, a3, ← h r]
  have : (2 * (r : ℕ) + 1) + (2 * ((r.rev : Fin k) : ℕ) + 1) = 2 * k := by omega
  calc k * ∑ i ∈ (s r).1, 2 * i + (s r).1.card * (2 * ↑r + 1) +
        (k * ∑ i ∈ (s r).2, 2 * i + (s r).1.card * (2 * ((r.rev : Fin k) : ℕ) + 1))
      = k * ∑ i ∈ (s r).1, 2 * i + k * ∑ i ∈ (s r).2, 2 * i +
        (s r).1.card * ((2 * ↑r + 1) + (2 * ((r.rev : Fin k) : ℕ) + 1)) := by ring
    _ = _ := by rw [this]; ring

theorem pairs_mono {E E' : ℕ} (h : E ≤ E') : pairs E ⊆ pairs E' := fun s hs => by
  rw [mem_pairs] at hs ⊢
  exact ⟨hs.1, hs.2.trans h⟩

theorem pairs_pos (E : ℕ) : 0 < (pairs E).card :=
  Finset.card_pos.2 ⟨(∅, ∅), mem_pairs.2 ⟨rfl, by simp [en]⟩⟩

theorem two_le_pairs : 2 ≤ (pairs 2).card := by
  have : ({(∅, ∅), ({0}, {0})} : Finset (Finset ℕ × Finset ℕ)) ⊆ pairs 2 := by
    intro s hs
    rw [mem_insert, mem_singleton] at hs
    rw [mem_pairs]
    rcases hs with rfl | rfl <;> simp [en]
  refine le_trans ?_ (card_le_card this)
  rw [card_insert_of_notMem, card_singleton]
  simp

/-- The sets of energy at most `E`. -/
def sets (E : ℕ) : Finset (Finset ℕ) := (range E).powerset.filter fun S => en S ≤ E

/-- "A state is a pair of such sets." -/
theorem card_pairs_le (E : ℕ) : (pairs E).card ≤ (sets E).card * (sets E).card := by
  rw [← card_product]
  refine card_le_card fun s hs => ?_
  unfold pairs at hs
  rw [mem_filter, mem_product] at hs
  rw [mem_product, sets, mem_filter, mem_filter]
  exact ⟨⟨hs.1.1, by omega⟩, hs.1.2, by omega⟩

/-- The logarithm of the number of states. -/
noncomputable def lp (E : ℕ) : ℝ := Real.log (pairs E).card

theorem lp_nonneg (E : ℕ) : 0 ≤ lp E := Real.log_natCast_nonneg _

theorem lp_zero : lp 0 = 0 := by
  have : pairs 0 = {(∅, ∅)} := by
    ext s
    rw [mem_pairs, mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      have h1 : s.1 = ∅ := by
        by_contra hne
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
        exact absurd (lt_of_mem_en (E := 0) (by omega) hi) (by omega)
      have h2 : s.2 = ∅ := by
        by_contra hne
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
        exact absurd (lt_of_mem_en (E := 0) (by omega) hi) (by omega)
      exact Prod.ext h1 h2
    · rintro rfl
      simp [en]
  rw [lp, this]
  simp

theorem lp_mono {E E' : ℕ} (h : E ≤ E') : lp E ≤ lp E' :=
  Real.log_le_log (by exact_mod_cast pairs_pos E) (by exact_mod_cast card_le_card (pairs_mono h))

end Nc.Cross
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Two crossing wires": states
-/

namespace Paper

open Finset Filter Nc.Cross

/-- The number P(E) of states of energy at most E. -/
def stateCount (E : ℕ) : ℕ := (pairs E).card

/-- "A state is a pair (I, J) of finite subsets of ℕ = {0, 1, …} with |I| = |J|; this number is its size, and its energy is
∑_{i∈I} (2i+1) + ∑_{j∈J} (2j+1)." The theorem says which pairs are counted by P(E): the states of energy at most E. -/
theorem mem_states {E : ℕ} (s : Finset ℕ × Finset ℕ) :
    s ∈ pairs E ↔ s.1.card = s.2.card ∧ ∑ i ∈ s.1, (2 * i + 1) + ∑ j ∈ s.2, (2 * j + 1) ≤ E := mem_pairs

/-- Proof of Lemma lem:count: "Interleave k states: put ki+r into I for i ∈ I_r, and kj+k−1−r into J for j ∈ J_r. This is
injective and multiplies the total energy by k, so P(k²E) ≥ P(E)^k." -/
theorem lem_count_interleave (k E : ℕ) : stateCount E ^ k ≤ stateCount (k ^ 2 * E) := by
  rw [pow_two]
  show (pairs E).card ^ k ≤ (pairs (k * k * E)).card
  have h1 : (Fintype.piFinset fun _ : Fin k => pairs E).card = (pairs E).card ^ k := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← h1]
  refine Finset.card_le_card_of_injOn
    (fun s => (glueSet k fun r => (s r).1, glueSet k fun r => (s r.rev).2)) ?_ ?_
  · intro s hs
    have hs' : ∀ r, (s r).1.card = (s r).2.card ∧ en (s r).1 + en (s r).2 ≤ E := fun r =>
      mem_pairs.1 (Fintype.mem_piFinset.1 hs r)
    refine mem_coe.2 (mem_pairs.2 ⟨?_, ?_⟩)
    · show (glueSet k fun r => (s r).1).card = (glueSet k fun r => (s r.rev).2).card
      rw [card_glueSet, card_glueSet]
      refine Eq.trans ?_ (Fintype.sum_equiv Fin.revPerm (fun r => (s r.rev).2.card) (fun r => (s r).2.card)
        (fun r => by simp)).symm
      exact Finset.sum_congr rfl fun r _ => (hs' r).1
    · show en (glueSet k fun r => (s r).1) + en (glueSet k fun r => (s r.rev).2) ≤ _
      rw [en_glueSet s fun r => (hs' r).1, mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      calc ∑ r, (en (s r).1 + en (s r).2) ≤ ∑ _r : Fin k, E := Finset.sum_le_sum fun r _ => (hs' r).2
        _ = k * E := by simp
  · intro s _ s' _ h
    have h1 := glueSet_injective (Prod.ext_iff.1 h).1
    have h2 := glueSet_injective (Prod.ext_iff.1 h).2
    funext r
    refine Prod.ext (congrFun h1 r) ?_
    have := congrFun h2 r.rev
    simpa using this

/-- Proof of Lemma lem:count: "Let 0 < t < 1. The number of sets S with ∑_{i∈S} (2i+1) ≤ E is at most
t^(−E) ∏_i (1 + t^(2i+1)) ≤ t^(−E) e^(1/(1−t))." -/
theorem lem_count_sets (E : ℕ) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ((sets E).card : ℝ) * t ^ E ≤ Real.exp (1 / (1 - t)) := by
  calc ((sets E).card : ℝ) * t ^ E = ∑ _S ∈ sets E, t ^ E := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ S ∈ sets E, ∏ i ∈ S, t ^ (2 * i + 1) := by
        refine Finset.sum_le_sum fun S hS => ?_
        rw [Finset.prod_pow_eq_pow_sum]
        exact pow_le_pow_of_le_one h0.le h1.le (mem_filter.1 hS).2
    _ ≤ ∑ S ∈ (range E).powerset, ∏ i ∈ S, t ^ (2 * i + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun S _ _ =>
          Finset.prod_nonneg fun i _ => by positivity
    _ = ∏ i ∈ range E, (1 + t ^ (2 * i + 1)) := (Finset.prod_one_add _).symm
    _ ≤ ∏ i ∈ range E, Real.exp (t ^ i) := by
        refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
        have h2 : t ^ (2 * i + 1) ≤ t ^ i := pow_le_pow_of_le_one h0.le h1.le (by omega)
        have h3 := Real.add_one_le_exp (t ^ i)
        linarith
    _ = Real.exp (∑ i ∈ range E, t ^ i) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (1 / (1 - t)) := by
        refine Real.exp_le_exp.2 ?_
        rw [geom_sum_eq h1.ne, one_div, ← neg_div_neg_eq, neg_sub, neg_sub, div_eq_mul_inv]
        have : 0 ≤ (1 - t)⁻¹ := inv_nonneg.2 (by linarith)
        have h4 : 1 - t ^ E ≤ 1 := by
          have : 0 < t ^ E := by positivity
          linarith
        calc (1 - t ^ E) * (1 - t)⁻¹ ≤ 1 * (1 - t)⁻¹ := mul_le_mul_of_nonneg_right h4 this
          _ = _ := one_mul _

/-- Proof of Lemma lem:count: "as a state is a pair of such sets, 1 − t = 1/(2√E) gives ln P(E) ≤ 10√E for E ≥ 1." -/
theorem lem_count_upper {E : ℕ} (hE : 1 ≤ E) : Real.log (stateCount E) ≤ 10 * √E := by
  have hs1 : 1 ≤ √(E : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hE
  have hs0 : 0 < √(E : ℝ) := by linarith
  have hss : √(E : ℝ) * √(E : ℝ) = E := Real.mul_self_sqrt (Nat.cast_nonneg E)
  set t : ℝ := 1 - 1 / (2 * √(E : ℝ)) with ht
  have hx : 1 / (2 * √(E : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hx0 : 0 < 1 / (2 * √(E : ℝ)) := by positivity
  have ht0 : 0 < t := by linarith
  have ht1 : t < 1 := by linarith
  have h3 : (t ^ E)⁻¹ ≤ Real.exp √(E : ℝ) := by
    have h4 : t⁻¹ ≤ Real.exp (1 / √(E : ℝ)) := by
      refine le_trans ?_ (Real.add_one_le_exp (1 / √(E : ℝ)))
      rw [inv_le_iff_one_le_mul₀ ht0, ht]
      have e : (1 - 1 / (2 * √(E : ℝ))) * (1 / √(E : ℝ) + 1) - 1 =
          (√(E : ℝ) - 1) / (2 * (√(E : ℝ) * √(E : ℝ))) := by
        field_simp
        ring
      have : 0 ≤ (√(E : ℝ) - 1) / (2 * (√(E : ℝ) * √(E : ℝ))) := div_nonneg (by linarith) (by positivity)
      linarith
    rw [← inv_pow]
    calc t⁻¹ ^ E ≤ Real.exp (1 / √(E : ℝ)) ^ E := pow_le_pow_left₀ (by positivity) h4 _
      _ = Real.exp (E * (1 / √(E : ℝ))) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp √(E : ℝ) := by
          congr 1
          rw [mul_one_div, div_eq_iff hs0.ne', hss]
  have h2 : ((sets E).card : ℝ) ≤ Real.exp (5 * √(E : ℝ)) := by
    have h5 := lem_count_sets E ht0 ht1
    have h6 : 1 / (1 - t) = 2 * √(E : ℝ) := by
      rw [ht]
      field_simp
      ring
    rw [h6] at h5
    have htE : 0 < t ^ E := by positivity
    calc ((sets E).card : ℝ) = (sets E).card * t ^ E * (t ^ E)⁻¹ := by field_simp
      _ ≤ Real.exp (2 * √(E : ℝ)) * Real.exp √(E : ℝ) := mul_le_mul h5 h3 (by positivity) (Real.exp_pos _).le
      _ = Real.exp (3 * √(E : ℝ)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (5 * √(E : ℝ)) := Real.exp_le_exp.2 (by linarith)
  show lp E ≤ _
  rw [Nc.Cross.lp, Real.log_le_iff_le_exp (by exact_mod_cast pairs_pos E)]
  have h1 : ((pairs E).card : ℝ) ≤ (sets E).card * (sets E).card := by exact_mod_cast card_pairs_le E
  refine h1.trans ?_
  calc ((sets E).card : ℝ) * (sets E).card ≤ Real.exp (5 * Real.sqrt E) * Real.exp (5 * Real.sqrt E) :=
        mul_le_mul h2 h2 (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; ring_nf

/-- **Paper: Lemma lem:count.** "There is κ > 0 with ln P(E) ≤ κ√E for all E and ln P(E) ≥ (κ − o(1))√E for E → ∞." -/
theorem lem_count : ∃ κ : ℝ, 0 < κ ∧ (∀ E : ℕ, Real.log (stateCount E) ≤ κ * √E) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ E : ℕ in atTop, (κ - ε) * √E ≤ Real.log (stateCount E) := by
  have mul_lp_le : ∀ k E : ℕ, k * lp E ≤ lp (k * k * E) := by
    intro k E
    rw [Nc.Cross.lp, ← Real.log_pow, ← pow_two]
    refine Real.log_le_log (by have := pairs_pos E; positivity) ?_
    exact_mod_cast lem_count_interleave k E
  show ∃ κ : ℝ, 0 < κ ∧ (∀ E : ℕ, lp E ≤ κ * √E) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ E : ℕ in atTop, (κ - ε) * √E ≤ lp E
  set S : Set ℝ := {z | ∃ E : ℕ, 1 ≤ E ∧ z = lp E / Real.sqrt E} with hS
  have hb : BddAbove S := by
    refine ⟨10, ?_⟩
    rintro _ ⟨E, hE, rfl⟩
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hE))]
    exact lem_count_upper hE
  have hne : S.Nonempty := ⟨_, 1, le_rfl, rfl⟩
  have hle : ∀ E : ℕ, 1 ≤ E → lp E ≤ sSup S * Real.sqrt E := by
    intro E hE
    rw [← div_le_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hE))]
    exact le_csSup hb ⟨E, hE, rfl⟩
  have hpos : 0 < sSup S := by
    have h2 : 0 < lp 2 := Real.log_pos (by exact_mod_cast two_le_pairs)
    have : 0 < lp 2 / Real.sqrt (2 : ℕ) := div_pos h2 (Real.sqrt_pos.2 (by norm_num))
    exact this.trans_le (le_csSup hb ⟨2, by norm_num, rfl⟩)
  refine ⟨sSup S, hpos, fun E => ?_, fun ε hε => eventually_atTop.2 ?_⟩
  · rcases Nat.eq_zero_or_pos E with rfl | hE
    · simp [lp_zero]
    · exact hle E hE
  · obtain ⟨_, ⟨E₁, hE₁, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne (show sSup S - ε / 2 < sSup S by linarith)
    set c := sSup S with hc
    have hs1 : 0 < Real.sqrt E₁ := Real.sqrt_pos.2 (by exact_mod_cast hE₁)
    rw [lt_div_iff₀ hs1] at hlt
    refine ⟨⌈(2 * c * Real.sqrt E₁ / ε) ^ 2⌉₊, fun E hE => ?_⟩
    have hE' : 2 * c * Real.sqrt E₁ / ε ≤ Real.sqrt E := by
      refine Real.le_sqrt_of_sq_le ?_
      exact (Nat.le_ceil _).trans (by exact_mod_cast hE)
    rw [div_le_iff₀ hε] at hE'
    rcases le_or_gt c ε with hcε | hcε
    · have : (c - ε) * Real.sqrt E ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _)
      exact this.trans (lp_nonneg E)
    set k := Nat.sqrt (E / E₁) with hk
    have hk1 : k * k * E₁ ≤ E :=
      (Nat.mul_le_mul_right _ (Nat.sqrt_le _)).trans (Nat.div_mul_le_self _ _)
    have hk2 : E < (k + 1) * (k + 1) * E₁ := by
      have := Nat.lt_succ_sqrt (E / E₁)
      exact (Nat.div_lt_iff_lt_mul hE₁).1 this
    have hk3 : Real.sqrt E ≤ (k + 1) * Real.sqrt E₁ := by
      rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      have : (E : ℝ) ≤ ((k + 1) * (k + 1) * E₁ : ℕ) := by exact_mod_cast hk2.le
      push_cast at this
      nlinarith
    have h5 : k * lp E₁ ≤ lp E := (mul_lp_le k E₁).trans (lp_mono hk1)
    have h6 : (k : ℝ) * ((c - ε / 2) * Real.sqrt E₁) ≤ k * lp E₁ :=
      mul_le_mul_of_nonneg_left hlt.le (Nat.cast_nonneg _)
    have h7 : (c - ε / 2) * Real.sqrt E ≤ (c - ε / 2) * ((k + 1) * Real.sqrt E₁) :=
      mul_le_mul_of_nonneg_left hk3 (by linarith)
    have h8 : 0 ≤ ε / 2 * Real.sqrt E₁ := by positivity
    nlinarith

end Paper
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Two families of polynomials

`mB y r n = [tⁿ] (1+t)^r/(1+yt)^(r+1)`, `mC y r n = [tⁿ] (1+yt)^r/(1+t)^(r+1)`.
That these are the coefficients, the relation between the two families and the orthogonality relation are
Paper.meixner_B, meixner_C, meixner_reciprocal and eq_orth (Paper/Identity.lean).
-/

namespace Nc.Cross

variable {R : Type*} [CommRing R]

/-- `[tⁿ] (1+t)^r/(1+yt)^(r+1)`. -/
def mB (y : R) : ℕ → ℕ → R
  | 0, n => (-y) ^ n
  | _ + 1, 0 => 1
  | r + 1, n + 1 => mB y r (n + 1) + mB y r n - y * mB y (r + 1) n
termination_by r n => (r, n)

/-- `[tⁿ] (1+yt)^r/(1+t)^(r+1)`. -/
def mC (y : R) : ℕ → ℕ → R
  | 0, n => (-1) ^ n
  | _ + 1, 0 => 1
  | r + 1, n + 1 => mC y r (n + 1) + y * mC y r n - mC y (r + 1) n
termination_by r n => (r, n)

theorem mB_zero (y : R) (n : ℕ) : mB y 0 n = (-y) ^ n := by rw [mB]

theorem mB_zero_right (y : R) (r : ℕ) : mB y r 0 = 1 := by
  cases r with
  | zero => rw [mB, pow_zero]
  | succ r => rw [mB]

theorem mB_succ (y : R) (r n : ℕ) :
    mB y (r + 1) (n + 1) = mB y r (n + 1) + mB y r n - y * mB y (r + 1) n := by rw [mB]

theorem mC_zero (y : R) (n : ℕ) : mC y 0 n = (-1) ^ n := by rw [mC]

theorem mC_zero_right (y : R) (r : ℕ) : mC y r 0 = 1 := by
  cases r with
  | zero => rw [mC, pow_zero]
  | succ r => rw [mC]

theorem mC_succ (y : R) (r n : ℕ) :
    mC y (r + 1) (n + 1) = mC y r (n + 1) + y * mC y r n - mC y (r + 1) n := by rw [mC]

theorem map_mB {S : Type*} [CommRing S] (f : R →+* S) (y : R) (r n : ℕ) :
    f (mB y r n) = mB (f y) r n := by
  induction r generalizing n with
  | zero => simp [mB_zero]
  | succ r ih =>
    induction n with
    | zero => simp [mB_zero_right]
    | succ n ih' => simp [mB_succ, ih, ih']

theorem map_mC {S : Type*} [CommRing S] (f : R →+* S) (y : R) (r n : ℕ) :
    f (mC y r n) = mC (f y) r n := by
  induction r generalizing n with
  | zero => simp [mC_zero]
  | succ r ih =>
    induction n with
    | zero => simp [mC_zero_right]
    | succ n ih' => simp [mC_succ, ih, ih']

end Nc.Cross
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The determinant `Ψ`

Four sites `a, b, c, d`; a word at a site is a pair (rows, columns) of tuples of natural numbers. `Ψ` is the
determinant of a matrix over `ℤ[x]`, `y = x²`, with the blocks (rows `a, d | c, b`, columns `a, d | c, b`)
`ad: C`, `cb: -(y-1)C`, `ac: Λ`, `ab: (y-1)ΛB`, `dc: BᵀΛ`, `db: -Λ`, and minus the transposes.
-/

namespace Nc.Cross

open Matrix Finset

/-- Words: rows and columns at a site. -/
abbrev Wd (μ : ℕ) := (Fin μ → ℕ) × (Fin μ → ℕ)

section blocks

variable {R : Type*} [CommRing R] {μ ν : ℕ}

/-- The block of rows and columns at `a, d`: the paper's `M₁`. -/
def blX (x : R) (sa : Wd μ) (sd : Wd ν) : Matrix (Fin μ ⊕ Fin ν) (Fin μ ⊕ Fin ν) R :=
  fromBlocks 0 (of fun i j => mC (x ^ 2) (sa.1 i) (sd.2 j))
    (of fun i j => -mC (x ^ 2) (sa.2 j) (sd.1 i)) 0

/-- The block of rows and columns at `c, b`: the paper's `M₂`. -/
def blY (x : R) (sc : Wd μ) (sb : Wd ν) : Matrix (Fin μ ⊕ Fin ν) (Fin μ ⊕ Fin ν) R :=
  fromBlocks 0 (of fun i j => -((x ^ 2 - 1) * mC (x ^ 2) (sc.1 i) (sb.2 j)))
    (of fun i j => (x ^ 2 - 1) * mC (x ^ 2) (sc.2 j) (sb.1 i)) 0

/-- The block of rows at `a, d` and columns at `c, b`. -/
def blU (x : R) (sa : Wd μ) (sd : Wd ν) (sc : Wd μ) (sb : Wd ν) :
    Matrix (Fin μ ⊕ Fin ν) (Fin μ ⊕ Fin ν) R :=
  fromBlocks (of fun i j => if sa.1 i = sc.2 j then x ^ (2 * sa.1 i + 1) else 0)
    (of fun i j => (x ^ 2 - 1) * (x ^ (2 * sa.1 i + 1) * mB (x ^ 2) (sa.1 i) (sb.2 j)))
    (of fun i j => x ^ (2 * sc.2 j + 1) * mB (x ^ 2) (sc.2 j) (sd.1 i))
    (of fun i j => -(if sd.1 i = sb.2 j then x ^ (2 * sd.1 i + 1) else 0))

/-- The paper's matrix **M**, with the rows and the columns in the order `a, d | c, b`. -/
def matM (x : R) (sa : Wd μ) (sb : Wd ν) (sc : Wd μ) (sd : Wd ν) :
    Matrix ((Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν)) ((Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν)) R :=
  fromBlocks (blX x sa sd) (blU x sa sd sc sb)
    (-(blU x sa.swap sd.swap sc.swap sb.swap)ᵀ) (blY x sc sb)

/-- The paper's `Ψ = det M`. -/
def psi (x : R) (sa : Wd μ) (sb : Wd ν) (sc : Wd μ) (sd : Wd ν) : R := (matM x sa sb sc sd).det

theorem map_matM {S : Type*} [CommRing S] (f : R →+* S) (x : R) (sa : Wd μ) (sb : Wd ν) (sc : Wd μ)
    (sd : Wd ν) : f.mapMatrix (matM x sa sb sc sd) = matM (f x) sa sb sc sd := by
  ext i j
  rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;>
    simp [matM, blX, blY, blU, map_mB, map_mC, apply_ite f]

theorem map_psi {S : Type*} [CommRing S] (f : R →+* S) (x : R) (sa : Wd μ) (sb : Wd ν) (sc : Wd μ)
    (sd : Wd ν) : f (psi x sa sb sc sd) = psi (f x) sa sb sc sd := by
  rw [psi, psi, RingHom.map_det, map_matM]

/-- The paper's `F`: the rows `([r = i])_{r<K}` for `i ∈ I_a` and `(B(r,i))_{r<K}` for `i ∈ I_d`. -/
def facA (K : ℕ) (x : R) (sa : Wd μ) (sd : Wd ν) : Matrix (Fin μ ⊕ Fin ν) (Fin K) R :=
  of (Sum.elim (fun i r => if sa.1 i = (r : ℕ) then 1 else 0) fun i r => mB (x ^ 2) r (sd.1 i))

/-- The paper's `G`: the columns `([r = j])_{r<K}` for `j ∈ J_c` and `((y−1)B(r,j))_{r<K}` for `j ∈ J_b`. -/
def facB (K : ℕ) (x : R) (sc : Wd μ) (sb : Wd ν) : Matrix (Fin K) (Fin μ ⊕ Fin ν) R :=
  of fun r => Sum.elim (fun j => if (r : ℕ) = sc.2 j then 1 else 0)
    fun j => (x ^ 2 - 1) * mB (x ^ 2) r (sb.2 j)

theorem sum_ite_val (K n : ℕ) (f : ℕ → R) :
    ∑ r : Fin K, (if n = (r : ℕ) then f r else 0) = if n < K then f n else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun r => if n = r then f r else 0) K, Finset.sum_ite_eq]
  simp

end blocks

/-- Congruent matrices have congruent determinants. -/
theorem dvd_det_sub {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] (d : R) (M N : Matrix n n R)
    (h : ∀ i j, d ∣ M i j - N i j) : d ∣ M.det - N.det := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact h i j

end Nc.Cross
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Inversion `x ↦ 1/x` exchanges `b` and `d`: the multipliers

Definitions for the step "Reflection" of the proof of Proposition prop:identity (Paper/Identity.lean).
-/

set_option linter.unusedSimpArgs false

namespace Nc.Cross

open Matrix Finset

section inv

variable {R : Type*} [CommRing R] {μ ν : ℕ}

/-- The exchange of the sites `b` and `d`. -/
def exch (μ ν : ℕ) : (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν) ≃ (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν) where
  toFun
    | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inr (Sum.inr i) => Sum.inl (Sum.inr i)
  invFun
    | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inr (Sum.inr i) => Sum.inl (Sum.inr i)
  left_inv := by rintro ((i | i) | (i | i)) <;> rfl
  right_inv := by rintro ((i | i) | (i | i)) <;> rfl

/-- The multipliers of the rows (columns) of the matrix at `1/x`: `x^(2i+1)` at `a, c`, `(y−1)y^i` at `d` and `y^(i+1)` at `b`,
with `y = x²`. -/
def scal (x : R) (fa : Fin μ → ℕ) (fb : Fin ν → ℕ) (fc : Fin μ → ℕ) (fd : Fin ν → ℕ) :
    (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν) → R :=
  Sum.elim (Sum.elim (fun i => x ^ (2 * fa i + 1)) fun i => (x ^ 2 - 1) * (x ^ 2) ^ fd i)
    (Sum.elim (fun i => x ^ (2 * fc i + 1)) fun i => (x ^ 2) ^ (fb i + 1))

/-- The multipliers on the other side: `1 − y` at the new site `d`. -/
def scal' (x : R) : (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν) → R :=
  Sum.elim (Sum.elim (fun _ => 1) fun _ => 1) (Sum.elim (fun _ => 1) fun _ => 1 - x ^ 2)

/-- The energy of a word. -/
def enW (s : Wd μ) : ℕ := ∑ i, (2 * s.1 i + 1) + ∑ i, (2 * s.2 i + 1)

theorem prod_scal (x : R) (fa : Fin μ → ℕ) (fb : Fin ν → ℕ) (fc : Fin μ → ℕ) (fd : Fin ν → ℕ) :
    ∏ i, scal x fa fb fc fd i = (x ^ 2 - 1) ^ ν *
      x ^ ((∑ i, (2 * fa i + 1)) + (∑ i, (2 * fc i + 1)) + (∑ i, 2 * fd i) + ∑ i, (2 * fb i + 2)) := by
  simp only [scal, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  have e : ∀ i, 2 * (fb i + 1) = 2 * fb i + 2 := fun i => by ring
  simp only [e, pow_add]
  ring

theorem prod_scal' (x : R) :
    ∏ i, (scal' x : (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν) → R) i = (1 - x ^ 2) ^ ν := by
  simp [scal', Fintype.prod_sum_type]

end inv

end Nc.Cross
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The value at `x = 1`: a determinant
-/

namespace Nc.Cross

open Matrix Finset

/-- The matrix of coincidences of two increasing tuples. -/
theorem det_coinc {R : Type*} [CommRing R] {μ : ℕ} (f g : Fin μ → ℕ) (hf : StrictMono f) (hg : StrictMono g) :
    (of fun i j => if f i = g j then (1 : R) else 0).det = if f = g then 1 else 0 := by
  by_cases h : f = g
  · subst h
    rw [if_pos rfl]
    have : (of fun i j => if f i = f j then (1 : R) else 0) = (1 : Matrix (Fin μ) (Fin μ) R) := by
      ext i j
      simp [Matrix.one_apply, hf.injective.eq_iff]
    rw [this, det_one]
  · rw [if_neg h]
    have hr : ¬ Set.range f ⊆ Set.range g := by
      intro hsub
      apply h
      have hfin : Set.range f = Set.range g := by
        have h1 : (Finset.univ.image f) ⊆ (Finset.univ.image g) := by
          intro n hn
          have : n ∈ Set.range g := hsub (by simpa using hn)
          simpa using this
        have h2 := Finset.eq_of_subset_of_card_le h1 (by
          rw [Finset.card_image_of_injective _ hf.injective, Finset.card_image_of_injective _ hg.injective])
        have h3 := congrArg (fun s : Finset ℕ => (s : Set ℕ)) h2
        simpa using h3
      exact StrictMono.range_inj hf hg |>.1 hfin
    rw [Set.not_subset] at hr
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hr
    refine det_eq_zero_of_row_eq_zero i fun j => ?_
    simp only [of_apply]
    rw [if_neg]
    intro hij
    exact hi ⟨j, hij.symm⟩

end Nc.Cross
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The states of given size and energy, as words

The index sets of Paper.prop_identity (Paper/Identity.lean).
-/

namespace Nc.Cross

open Finset

/-- The states of size `μ` and energy `e`. -/
def states (μ e : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (pairs e).filter fun s => s.1.card = μ ∧ s.2.card = μ ∧ en s.1 + en s.2 = e

section word

variable {μ e : ℕ}

theorem states_prop (s : ↥(states μ e)) :
    s.1.1.card = μ ∧ s.1.2.card = μ ∧ en s.1.1 + en s.1.2 = e := (mem_filter.1 s.2).2

/-- The word of a state. -/
def word (s : ↥(states μ e)) : Wd μ :=
  (s.1.1.orderEmbOfFin (states_prop s).1, s.1.2.orderEmbOfFin (states_prop s).2.1)

theorem word_strictMono (s : ↥(states μ e)) : StrictMono (word s).1 ∧ StrictMono (word s).2 :=
  ⟨(s.1.1.orderEmbOfFin (states_prop s).1).strictMono, (s.1.2.orderEmbOfFin (states_prop s).2.1).strictMono⟩

theorem word_injective : Function.Injective (word : ↥(states μ e) → Wd μ) := by
  intro s s' h
  have h1 : ((s.1.1 : Finset ℕ) : Set ℕ) = s'.1.1 := by
    rw [← Finset.range_orderEmbOfFin _ (states_prop s).1, ← Finset.range_orderEmbOfFin _ (states_prop s').1]
    exact congrArg Set.range (Prod.ext_iff.1 h).1
  have h2 : ((s.1.2 : Finset ℕ) : Set ℕ) = s'.1.2 := by
    rw [← Finset.range_orderEmbOfFin _ (states_prop s).2.1, ← Finset.range_orderEmbOfFin _ (states_prop s').2.1]
    exact congrArg Set.range (Prod.ext_iff.1 h).2
  exact Subtype.ext (Prod.ext (Finset.coe_injective h1) (Finset.coe_injective h2))

theorem sum_orderEmb (S : Finset ℕ) {k : ℕ} (h : S.card = k) :
    ∑ i, (2 * S.orderEmbOfFin h i + 1) = en S := by
  conv_rhs => rw [en, ← Finset.map_orderEmbOfFin_univ S h, Finset.sum_map]
  rfl

theorem enW_word (s : ↥(states μ e)) : enW (word s) = e := by
  rw [enW, word, sum_orderEmb, sum_orderEmb]
  exact (states_prop s).2.2

theorem enW_swap (w : Wd μ) : enW w.swap = enW w := by
  rw [enW, enW, add_comm]
  rfl

end word

end Nc.Cross
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Two crossing wires": the identity

The polynomials B(r,n) and C(r,n) are Nc.Cross.mB and mC (with y an element of a ring), the matrix M is Nc.Cross.matM and
Ψ = det M is Nc.Cross.psi. A state enters them as the pair of the increasing enumerations of its two sets (Nc.Cross.word).
-/

set_option linter.unusedSimpArgs false

namespace Paper

open Finset Matrix Nc.Cross

/-- "Fix sizes μ, ν and energies e₁, e₂, and let Σ₁, Σ₂ be the sets of states with size and energy (μ, e₁), respectively (ν, e₂)":
the set Nc.Cross.states μ e. -/
theorem mem_stateClass {μ e : ℕ} (s : Finset ℕ × Finset ℕ) :
    s ∈ states μ e ↔ s.1.card = μ ∧ s.2.card = μ ∧ ∑ i ∈ s.1, (2 * i + 1) + ∑ j ∈ s.2, (2 * j + 1) = e := by
  rw [states, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_pairs.2 ⟨h.1.trans h.2.1.symm, h.2.2.le⟩, h⟩⟩

section Orth

variable {A : Type*} [CommRing A]

/-- The coefficients of a power series times 1 + at. -/
private theorem coeff_mk_mul_zero (f : ℕ → A) (a : A) :
    PowerSeries.coeff 0 (PowerSeries.mk f * (1 + PowerSeries.C a * PowerSeries.X)) = f 0 := by
  simp [mul_add, ← mul_assoc]

private theorem coeff_mk_mul_succ (f : ℕ → A) (a : A) (n : ℕ) :
    PowerSeries.coeff (n + 1) (PowerSeries.mk f * (1 + PowerSeries.C a * PowerSeries.X)) = f (n + 1) + f n * a := by
  simp [mul_add, ← mul_assoc, PowerSeries.coeff_succ_mul_X]

/-- "Let B(r,n) and C(r,n) be the coefficients of tⁿ in (1+t)^r/(1+yt)^(r+1) and (1+yt)^r/(1+t)^(r+1)." For B: the recursion
that defines Nc.Cross.mB gives the coefficients of the first series. -/
theorem meixner_B (y : A) (r : ℕ) :
    PowerSeries.mk (mB y r) * (1 + PowerSeries.C y * PowerSeries.X) ^ (r + 1) = (1 + PowerSeries.X) ^ r := by
  induction r with
  | zero =>
    rw [zero_add, pow_one, pow_zero]
    ext n
    cases n with
    | zero => rw [coeff_mk_mul_zero, mB_zero]; simp
    | succ n => rw [coeff_mk_mul_succ, mB_zero, mB_zero, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n)]; ring
  | succ r ih =>
    have step : PowerSeries.mk (mB y (r + 1)) * (1 + PowerSeries.C y * PowerSeries.X) =
        PowerSeries.mk (mB y r) * (1 + PowerSeries.C 1 * PowerSeries.X) := by
      ext n
      cases n with
      | zero => rw [coeff_mk_mul_zero, coeff_mk_mul_zero, mB_zero_right, mB_zero_right]
      | succ n => rw [coeff_mk_mul_succ, coeff_mk_mul_succ, mB_succ]; ring
    rw [map_one, one_mul] at step
    rw [pow_succ' _ (r + 1), ← mul_assoc, step, mul_right_comm, ih, pow_succ]

/-- The same sentence for C: the recursion that defines Nc.Cross.mC gives the coefficients of (1+yt)^r/(1+t)^(r+1). -/
theorem meixner_C (y : A) (r : ℕ) :
    PowerSeries.mk (mC y r) * (1 + PowerSeries.X) ^ (r + 1) = (1 + PowerSeries.C y * PowerSeries.X) ^ r := by
  have one : (1 + PowerSeries.X : PowerSeries A) = 1 + PowerSeries.C 1 * PowerSeries.X := by rw [map_one, one_mul]
  induction r with
  | zero =>
    rw [zero_add, pow_one, pow_zero, one]
    ext n
    cases n with
    | zero => rw [coeff_mk_mul_zero, mC_zero]; simp
    | succ n => rw [coeff_mk_mul_succ, mC_zero, mC_zero, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n)]; ring
  | succ r ih =>
    have step : PowerSeries.mk (mC y (r + 1)) * (1 + PowerSeries.X) =
        PowerSeries.mk (mC y r) * (1 + PowerSeries.C y * PowerSeries.X) := by
      rw [one]
      ext n
      cases n with
      | zero => rw [coeff_mk_mul_zero, coeff_mk_mul_zero, mC_zero_right, mC_zero_right]
      | succ n => rw [coeff_mk_mul_succ, coeff_mk_mul_succ, mC_succ]; ring
    rw [pow_succ' _ (r + 1), ← mul_assoc, step, mul_right_comm, ih, pow_succ]

/-- "They are polynomials in y, and yⁿ B(r,n)|_{1/y} = C(r,n)." Here z is an inverse of y. -/
theorem meixner_reciprocal {y z : A} (h : y * z = 1) (r n : ℕ) : y ^ n * mB z r n = mC y r n := by
  induction r generalizing n with
  | zero =>
    rw [mB_zero, mC_zero, ← mul_pow, mul_neg, h]
  | succ r ih =>
    induction n with
    | zero => simp [mB_zero_right, mC_zero_right]
    | succ n ih' =>
      rw [mB_succ, mC_succ, ← ih, ← ih, ← ih']
      linear_combination (-(y ^ n * mB z (r + 1) n)) * h

/-- The same relation read backwards: yⁿ C(r,n)|_{1/y} = B(r,n). -/
theorem meixner_reciprocal' {y z : A} (h : y * z = 1) (r n : ℕ) : y ^ n * mC z r n = mB y r n := by
  have h' : z * y = 1 := by rw [mul_comm, h]
  rw [← meixner_reciprocal h', ← mul_assoc, ← mul_pow, h, one_pow, one_mul]

/-- The telescoping sum. -/
private theorem tele (y : A) (u v : ℕ → A) (R : ℕ) (h : ∀ r, v (r + 1) = u r) :
    ∑ r ∈ Finset.range R, y ^ r * (v r - y * u r) = v 0 - y ^ R * v R := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, ih, h]
    ring

/-- **Paper: display eq:orth.** "(1−y) ∑_{r<R} y^r B(r,i) B(r,j) ≡ [i=j] y^i (mod y^R)." Here y is any element of any
commutative ring; the paper's case is the variable y of ℤ[y]. -/
theorem eq_orth (y : A) (R i j : ℕ) :
    y ^ R ∣ (1 - y) * ∑ r ∈ Finset.range R, y ^ r * (mB y r i * mB y r j)
      - (if i = j then y ^ i else 0) := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero =>
      have := tele y (fun _ => (1 : A)) (fun _ => 1) R (fun _ => rfl)
      refine ⟨-1, ?_⟩
      simp only [mB_zero_right, mul_one, if_true, pow_zero]
      simp only [mul_one] at this
      rw [← Finset.sum_mul] at this
      linear_combination this
    | succ j =>
      have := tele y (fun r => mB y r (j + 1) + mB y r j) (fun r => mB y r (j + 1) + y * mB y r j) R
        (fun r => by rw [mB_succ]; ring)
      refine ⟨-(mB y R (j + 1) + y * mB y R j), ?_⟩
      simp only [mB_zero_right, one_mul, (Nat.succ_ne_zero j).symm, if_false, mB_zero] at this ⊢
      rw [Finset.mul_sum]
      have e : ∑ r ∈ Finset.range R, (1 - y) * (y ^ r * mB y r (j + 1)) =
          ∑ r ∈ Finset.range R, y ^ r * (mB y r (j + 1) + y * mB y r j
            - y * (mB y r (j + 1) + mB y r j)) :=
        Finset.sum_congr rfl fun r _ => by ring
      rw [e, this]
      ring
  | succ i ih =>
    cases j with
    | zero =>
      have := tele y (fun r => mB y r (i + 1) + mB y r i) (fun r => mB y r (i + 1) + y * mB y r i) R
        (fun r => by rw [mB_succ]; ring)
      refine ⟨-(mB y R (i + 1) + y * mB y R i), ?_⟩
      simp only [mB_zero_right, mul_one, Nat.succ_ne_zero i, if_false, mB_zero] at this ⊢
      rw [Finset.mul_sum]
      have e : ∑ r ∈ Finset.range R, (1 - y) * (y ^ r * mB y r (i + 1)) =
          ∑ r ∈ Finset.range R, y ^ r * (mB y r (i + 1) + y * mB y r i
            - y * (mB y r (i + 1) + mB y r i)) :=
        Finset.sum_congr rfl fun r _ => by ring
      rw [e, this]
      ring
    | succ j =>
      have := tele y
        (fun r => (mB y r (i + 1) + mB y r i) * (mB y r (j + 1) + mB y r j))
        (fun r => (mB y r (i + 1) + y * mB y r i) * (mB y r (j + 1) + y * mB y r j)) R
        (fun r => by rw [mB_succ, mB_succ]; ring)
      obtain ⟨w, hw⟩ := ih j
      refine ⟨y * w - (mB y R (i + 1) + y * mB y R i) * (mB y R (j + 1) + y * mB y R j), ?_⟩
      have e : ∑ r ∈ Finset.range R, y ^ r * ((mB y r (i + 1) + y * mB y r i) *
            (mB y r (j + 1) + y * mB y r j)
            - y * ((mB y r (i + 1) + mB y r i) * (mB y r (j + 1) + mB y r j))) =
          (1 - y) * ∑ r ∈ Finset.range R, y ^ r * (mB y r (i + 1) * mB y r (j + 1))
          - y * ((1 - y) * ∑ r ∈ Finset.range R, y ^ r * (mB y r i * mB y r j)) := by
        simp only [Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun r _ => by ring
      rw [e] at this
      have z0 : (mB y 0 (i + 1) + y * mB y 0 i) = 0 := by simp only [mB_zero]; ring
      have z1 : (if i + 1 = j + 1 then y ^ (i + 1) else 0) = y * (if i = j then y ^ i else 0) := by
        by_cases hmn : i = j
        · simp [hmn, pow_succ, mul_comm]
        · simp [hmn]
      rw [z0, zero_mul, zero_sub] at this
      rw [z1]
      linear_combination this + y * hw

end Orth

section Blocks

variable {R : Type*} [CommRing R] {μ ν : ℕ}

/-- Proof of Proposition prop:identity, the coefficients: "So the block of rows a, d and columns c, b is congruent modulo X^(2R)
to FDG". Here F = facA, G = facB, K is the paper's R, and the block is Nc.Cross.blU; its part at (d,b) is treated by (eq:orth).
The other half, "and in the same way that of rows c, b and columns a, d to −G′DF′", is this theorem for the states with I and J
exchanged, transposed. -/
theorem prop_identity_blocks (K : ℕ) (x : R) (sa : Wd μ) (sd : Wd ν) (sc : Wd μ) (sb : Wd ν)
    (i j : Fin μ ⊕ Fin ν) :
    x ^ (2 * K) ∣ blU x sa sd sc sb i j -
      (facA K x sa sd * diagonal (fun r : Fin K => x ^ (2 * (r : ℕ) + 1)) * facB K x sc sb) i j := by
  have hdvd : ∀ n, ¬ n < K → x ^ (2 * K) ∣ x ^ (2 * n + 1) := fun n hn =>
    pow_dvd_pow x (by omega)
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.diagonal_mul]
  rcases i with i | i <;> rcases j with j | j
  · simp only [facA, facB, blU, of_apply, Sum.elim_inl, fromBlocks_apply₁₁, ite_mul, one_mul, zero_mul]
    rw [sum_ite_val K (sa.1 i) (fun r => x ^ (2 * r + 1) * if r = sc.2 j then 1 else 0)]
    by_cases h1 : sa.1 i < K
    · simp [h1]
    · by_cases h2 : sa.1 i = sc.2 j
      · rw [if_neg h1, if_pos h2, sub_zero]
        exact hdvd _ h1
      · simp [h1, h2]
  · simp only [facA, facB, blU, of_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₂, ite_mul, one_mul,
      zero_mul]
    rw [sum_ite_val K (sa.1 i) (fun r => x ^ (2 * r + 1) * ((x ^ 2 - 1) * mB (x ^ 2) r (sb.2 j)))]
    by_cases h1 : sa.1 i < K
    · rw [if_pos h1]
      exact ⟨0, by ring⟩
    · rw [if_neg h1, sub_zero]
      exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (hdvd _ h1) _) _
  · simp only [facA, facB, blU, of_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₂₁]
    have e : ∀ r : Fin K, mB (x ^ 2) r (sd.1 i) * (x ^ (2 * (r : ℕ) + 1) *
        if (r : ℕ) = sc.2 j then 1 else 0) =
        if sc.2 j = (r : ℕ) then (fun r => mB (x ^ 2) r (sd.1 i) * x ^ (2 * r + 1)) r else 0 := by
      intro r
      by_cases h : (r : ℕ) = sc.2 j
      · simp [h]
      · simp [h, Ne.symm h]
    rw [Finset.sum_congr rfl fun r _ => e r,
      sum_ite_val K (sc.2 j) (fun r => mB (x ^ 2) r (sd.1 i) * x ^ (2 * r + 1))]
    by_cases h1 : sc.2 j < K
    · rw [if_pos h1]
      exact ⟨0, by ring⟩
    · rw [if_neg h1, sub_zero]
      exact Dvd.dvd.mul_right (hdvd _ h1) _
  · simp only [facA, facB, blU, of_apply, Sum.elim_inr, fromBlocks_apply₂₂]
    obtain ⟨w, hw⟩ := eq_orth (x ^ 2) K (sd.1 i) (sb.2 j)
    refine ⟨x * w, ?_⟩
    have e : ∑ r : Fin K, mB (x ^ 2) r (sd.1 i) * (x ^ (2 * (r : ℕ) + 1) *
        ((x ^ 2 - 1) * mB (x ^ 2) r (sb.2 j))) =
        -(x * ((1 - x ^ 2) * ∑ r ∈ Finset.range K, (x ^ 2) ^ r * (mB (x ^ 2) r (sd.1 i) *
          mB (x ^ 2) r (sb.2 j)))) := by
      rw [Finset.sum_range, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← pow_mul, pow_succ]
      ring
    have z : (if sd.1 i = sb.2 j then x ^ (2 * sd.1 i + 1) else 0) =
        x * (if sd.1 i = sb.2 j then (x ^ 2) ^ sd.1 i else 0) := by
      split_ifs
      · rw [← pow_mul, pow_succ, mul_comm]
      · simp
    rw [e, z, pow_mul]
    linear_combination x * hw


/-- Proof of Proposition prop:identity, reflection: "Substitute 1/X for X and multiply the rows and the columns of a, c by
X^(2i+1), those of d by (y−1)y^i and those of b by y^(i+1). The relation between B and C shows that one obtains the matrix M in
which the sites b and d are exchanged (the new site d holds s_b), with the rows and columns of the new d multiplied by 1−y."
Entry by entry; z is the inverse of x, the multipliers are Nc.Cross.scal and scal', and exch exchanges the sites. -/
theorem prop_identity_exchange {x z : R} (h : x * z = 1) (sa : Wd μ) (sb : Wd ν) (sc : Wd μ) (sd : Wd ν)
    (i j : (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν)) :
    scal x sa.1 sb.1 sc.1 sd.1 i * (scal x sa.2 sb.2 sc.2 sd.2 j * matM z sa sb sc sd i j) =
      scal' x i * (scal' x j * (matM x sa sd sc sb).submatrix (exch μ ν) (exch μ ν) i j) := by
  have h2 : x ^ 2 * z ^ 2 = 1 := by rw [← mul_pow, h, one_pow]
  have hxz : ∀ n, x ^ n * z ^ n = 1 := fun n => by rw [← mul_pow, h, one_pow]
  have hB : ∀ r n, (x ^ 2) ^ n * mB (z ^ 2) r n = mC (x ^ 2) r n := meixner_reciprocal h2
  have hC : ∀ r n, (x ^ 2) ^ n * mC (z ^ 2) r n = mB (x ^ 2) r n := meixner_reciprocal' h2
  have hz : ∀ m : ℕ, x ^ (2 * m + 1) * z ^ (2 * m + 1) = 1 := fun m => hxz _
  rcases i with (i | i) | (i | i)
  · rcases j with (j | j) | (j | j)
    · simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap]
    · simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap]
      linear_combination (x ^ (2 * sa.1 i + 1) * (x ^ 2 - 1)) * hC (sa.1 i) (sd.2 j)
    · simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap]
      by_cases h1 : sa.1 i = sc.2 j
      · rw [if_pos h1, if_pos h1, ← h1]
        linear_combination x ^ (2 * sa.1 i + 1) * hz (sa.1 i)
      · simp [h1]
    · simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap]
      linear_combination (x ^ 2 * (z ^ 2 - 1) * ((x ^ 2) ^ sb.2 j * mB (z ^ 2) (sa.1 i) (sb.2 j))) *
        hz (sa.1 i) + (x ^ 2 * (z ^ 2 - 1)) * hB (sa.1 i) (sb.2 j) + mC (x ^ 2) (sa.1 i) (sb.2 j) * h2
  · rcases j with (j | j) | (j | j)
    · simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap]
      linear_combination (-(x ^ (2 * sa.2 j + 1) * (x ^ 2 - 1))) * hC (sa.2 j) (sd.1 i)
    · simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap]
    · simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap]
      linear_combination ((x ^ 2 - 1) * ((x ^ 2) ^ sd.1 i * mB (z ^ 2) (sc.2 j) (sd.1 i))) * hz (sc.2 j) +
        (x ^ 2 - 1) * hB (sc.2 j) (sd.1 i)
    · simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap]
      by_cases h1 : sd.1 i = sb.2 j
      · rw [if_pos h1, if_pos h1.symm, ← h1]
        linear_combination (x ^ (2 * sd.1 i + 1) * (1 - x ^ 2)) * hz (sd.1 i)
      · simp [h1, Ne.symm h1]
  · rcases j with (j | j) | (j | j)
    · simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap]
      by_cases h1 : sa.2 j = sc.1 i
      · rw [if_pos h1, if_pos h1, ← h1]
        linear_combination (-x ^ (2 * sa.2 j + 1)) * hz (sa.2 j)
      · simp [h1]
    · simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap]
      linear_combination (-(x ^ 2 - 1) * ((x ^ 2) ^ sd.2 j * mB (z ^ 2) (sc.1 i) (sd.2 j))) * hz (sc.1 i) -
        (x ^ 2 - 1) * hB (sc.1 i) (sd.2 j)
    · simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap]
    · simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap]
      linear_combination (-(x ^ (2 * sc.1 i + 1) * (1 - x ^ 2))) * hC (sc.1 i) (sb.2 j) -
        (x ^ (2 * sc.1 i + 1) * (x ^ 2) ^ sb.2 j * mC (z ^ 2) (sc.1 i) (sb.2 j)) * h2
  · rcases j with (j | j) | (j | j)
    · simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap]
      linear_combination (-(x ^ 2 * (z ^ 2 - 1) * ((x ^ 2) ^ sb.1 i * mB (z ^ 2) (sa.2 j) (sb.1 i)))) *
        hz (sa.2 j) - (x ^ 2 * (z ^ 2 - 1)) * hB (sa.2 j) (sb.1 i) - mC (x ^ 2) (sa.2 j) (sb.1 i) * h2
    · simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap]
      by_cases h1 : sd.2 j = sb.1 i
      · rw [if_pos h1, if_pos h1.symm, ← h1]
        linear_combination (x ^ (2 * sd.2 j + 1) * (x ^ 2 - 1)) * hz (sd.2 j)
      · simp [h1, Ne.symm h1]
    · simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap]
      linear_combination (x ^ (2 * sc.2 j + 1) * (1 - x ^ 2)) * hC (sc.2 j) (sb.1 i) +
        (x ^ (2 * sc.2 j + 1) * (x ^ 2) ^ sb.1 i * mC (z ^ 2) (sc.2 j) (sb.1 i)) * h2
    · simp only [matM, blX, blY, blU, scal, scal', exch, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero, Prod.fst_swap, Prod.snd_swap]

/-- Proof of Proposition prop:identity, reflection: "Rows and columns are permuted alike, so there is no sign." So the product of
all multipliers times Ψ(1/X; s_a, s_b, s_c, s_d) is (1−y)^(2ν) Ψ(X; s_a, s_d, s_c, s_b). -/
theorem prop_identity_exchange_det {x z : R} (h : x * z = 1) (sa : Wd μ) (sb : Wd ν) (sc : Wd μ) (sd : Wd ν) :
    (∏ i, scal x sa.1 sb.1 sc.1 sd.1 i) * ((∏ i, scal x sa.2 sb.2 sc.2 sd.2 i) * psi z sa sb sc sd) =
      (∏ i, (scal' x : (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν) → R) i) *
      ((∏ i, (scal' x : (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν) → R) i) * psi x sa sd sc sb) := by
  rw [psi, psi, ← det_submatrix_equiv_self (exch μ ν) (matM x sa sd sc sb),
    ← det_mul_row (scal x sa.2 sb.2 sc.2 sd.2) (matM z sa sb sc sd),
    ← det_mul_column (scal x sa.1 sb.1 sc.1 sd.1) (of fun i j => scal x sa.2 sb.2 sc.2 sd.2 j *
      matM z sa sb sc sd i j),
    ← det_mul_row (scal' x) ((matM x sa sd sc sb).submatrix (exch μ ν) (exch μ ν)),
    ← det_mul_column (scal' x) (of fun i j => scal' x j *
      (matM x sa sd sc sb).submatrix (exch μ ν) (exch μ ν) i j)]
  congr 1
  ext i j
  exact prop_identity_exchange h sa sb sc sd i j

/-- Proof of Proposition prop:identity, reflection: "The multipliers at a, c, d, b contain X to the powers e₁, e₁, e₂−2ν, e₂+2ν, in
all Θ, and the factors (y−1)^(2ν) and (1−y)^(2ν) on the two sides cancel in ℤ[X]. So
X^Θ Ψ(1/X; s_a, s_b, s_c, s_d) = Ψ(X; s_a, s_d, s_c, s_b)", Θ = 2(e₁+e₂).
Here x is an element of a domain with inverse z and x² ≠ 1; the paper's case is x = X in the field of fractions of ℤ[X]. -/
theorem prop_identity_reflection [IsDomain R] {x z : R} (h : x * z = 1) (h1 : x ^ 2 ≠ 1) (sa : Wd μ) (sb : Wd ν) (sc : Wd μ)
    (sd : Wd ν) {e₁ e₂ : ℕ} (ha : enW sa = e₁) (hb : enW sb = e₂) (hc : enW sc = e₁) (hd : enW sd = e₂) :
    x ^ (2 * (e₁ + e₂)) * psi z sa sb sc sd = psi x sa sd sc sb := by
  have key := prop_identity_exchange_det h sa sb sc sd
  rw [prod_scal, prod_scal, prod_scal'] at key
  have hne : (1 - x ^ 2) ^ ν * (1 - x ^ 2) ^ ν ≠ 0 := by
    have : (1 - x ^ 2) ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    exact mul_ne_zero (pow_ne_zero _ this) (pow_ne_zero _ this)
  refine mul_left_cancel₀ hne ?_
  have hs : (x ^ 2 - 1) ^ ν * (x ^ 2 - 1) ^ ν = (1 - x ^ 2) ^ ν * (1 - x ^ 2) ^ ν := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    ring
  have hν1 : ∀ f : Fin ν → ℕ, ∑ i, 2 * f i + ν = ∑ i, (2 * f i + 1) := fun f => by
    simp [Finset.sum_add_distrib]
  have hν2 : ∀ f : Fin ν → ℕ, ∑ i, (2 * f i + 2) = ∑ i, (2 * f i + 1) + ν := fun f => by
    simp [Finset.sum_add_distrib]
    ring
  have hexp : (∑ i, (2 * sa.1 i + 1)) + (∑ i, (2 * sc.1 i + 1)) + (∑ i, 2 * sd.1 i) +
      (∑ i, (2 * sb.1 i + 2)) + ((∑ i, (2 * sa.2 i + 1)) + (∑ i, (2 * sc.2 i + 1)) + (∑ i, 2 * sd.2 i) +
      ∑ i, (2 * sb.2 i + 2)) = 2 * (e₁ + e₂) := by
    unfold enW at ha hb hc hd
    have := hν1 sd.1
    have := hν1 sd.2
    have := hν2 sb.1
    have := hν2 sb.2
    omega
  generalize (∑ i, (2 * sa.1 i + 1)) + (∑ i, (2 * sc.1 i + 1)) + (∑ i, 2 * sd.1 i) +
    (∑ i, (2 * sb.1 i + 2)) = a at key hexp
  generalize (∑ i, (2 * sa.2 i + 1)) + (∑ i, (2 * sc.2 i + 1)) + (∑ i, 2 * sd.2 i) +
    (∑ i, (2 * sb.2 i + 2)) = b at key hexp
  rw [← hexp, pow_add]
  linear_combination key - (x ^ a * x ^ b * psi z sa sb sc sd) * hs

end Blocks

/-- Proof of Proposition prop:identity, X = 1: "for states in the given classes, Ψ|_{X=1} is a sign, depending on μ, ν only,
times [J_c = I_a, I_c = J_a, J_b = I_d, I_b = J_d]." -/
theorem prop_identity_one (μ ν : ℕ) : ∃ ε : ℤˣ, ∀ (sa : Wd μ) (sb : Wd ν) (sc : Wd μ) (sd : Wd ν),
    StrictMono sa.1 → StrictMono sa.2 → StrictMono sb.1 → StrictMono sb.2 →
    StrictMono sc.1 → StrictMono sc.2 → StrictMono sd.1 → StrictMono sd.2 →
    psi (1 : ℤ) sa sb sc sd = ε * if sa = sc.swap ∧ sb = sd.swap then 1 else 0 := by
  let e : Equiv.Perm ((Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν)) := Equiv.sumComm _ _
  refine ⟨Equiv.Perm.sign e * (-1) ^ (μ + ν), fun sa sb sc sd ha1 ha2 hb1 hb2 hc1 hc2 hd1 hd2 => ?_⟩
  have h1 := det_permute' e (matM (1 : ℤ) sa sb sc sd)
  have h2 : (matM (1 : ℤ) sa sb sc sd).submatrix id e =
      fromBlocks (blU (1 : ℤ) sa sd sc sb) (blX (1 : ℤ) sa sd) (blY (1 : ℤ) sc sb)
        (-(blU (1 : ℤ) sa.swap sd.swap sc.swap sb.swap)ᵀ) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [matM, e]
  have hY : blY (1 : ℤ) sc sb = 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [blY]
  have hU : ∀ (sa : Wd μ) (sd : Wd ν) (sc : Wd μ) (sb : Wd ν), StrictMono sa.1 → StrictMono sd.1 →
      StrictMono sc.2 → StrictMono sb.2 →
      (blU (1 : ℤ) sa sd sc sb).det = (-1) ^ ν * ((if sa.1 = sc.2 then 1 else 0) *
        (if sd.1 = sb.2 then 1 else 0)) := by
    intro sa sd sc sb k1 k2 k3 k4
    have e1 : blU (1 : ℤ) sa sd sc sb = fromBlocks (of fun i j => if sa.1 i = sc.2 j then 1 else 0) 0
        (of fun i j => mB 1 (sc.2 j) (sd.1 i)) (-(of fun i j => if sd.1 i = sb.2 j then 1 else 0)) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [blU]
    rw [e1, det_fromBlocks_zero₁₂, det_neg, Fintype.card_fin, det_coinc _ _ k1 k3, det_coinc _ _ k2 k4]
    ring
  rw [h2, hY, det_fromBlocks_zero₂₁, det_neg, det_transpose, hU _ _ _ _ ha1 hd1 hc2 hb2,
    hU _ _ _ _ ha2 hd2 hc1 hb1] at h1
  simp only [Prod.fst_swap, Prod.snd_swap, Fintype.card_sum, Fintype.card_fin] at h1
  have hs : ((Equiv.Perm.sign e : ℤˣ) : ℤ) * ((Equiv.Perm.sign e : ℤˣ) : ℤ) = 1 := Int.units_coe_mul_self _
  have hν : ((-1 : ℤ) ^ ν) * (-1) ^ ν = 1 := by rw [← mul_pow]; simp
  have hind : (if sa = sc.swap ∧ sb = sd.swap then (1 : ℤ) else 0) =
      ((if sa.1 = sc.2 then 1 else 0) * (if sd.1 = sb.2 then 1 else 0)) *
      ((if sa.2 = sc.1 then 1 else 0) * (if sd.2 = sb.1 then 1 else 0)) := by
    have : (sa = sc.swap ∧ sb = sd.swap) ↔
        ((sa.1 = sc.2 ∧ sd.1 = sb.2) ∧ (sa.2 = sc.1 ∧ sd.2 = sb.1)) := by
      rw [Prod.ext_iff, Prod.ext_iff]
      simp only [Prod.fst_swap, Prod.snd_swap]
      constructor
      · rintro ⟨⟨a, b⟩, c, d⟩
        exact ⟨⟨a, d.symm⟩, b, c.symm⟩
      · rintro ⟨⟨a, d⟩, b, c⟩
        exact ⟨⟨a, b⟩, c.symm, d.symm⟩
    simp only [this]
    by_cases a : sa.1 = sc.2 <;> by_cases b : sd.1 = sb.2 <;> by_cases c : sa.2 = sc.1 <;>
      by_cases d : sd.2 = sb.1 <;> simp [a, b, c, d]
  rw [psi, hind]
  push_cast
  linear_combination (-(matM (1 : ℤ) sa sb sc sd).det) * hs - ((Equiv.Perm.sign e : ℤˣ) : ℤ) * h1
    + ((Equiv.Perm.sign e : ℤˣ) : ℤ) * (-1) ^ (μ + ν) * (((if sa.1 = sc.2 then 1 else 0) * (if sd.1 = sb.2 then 1 else 0)) *
      ((if sa.2 = sc.1 then 1 else 0) * (if sd.2 = sb.1 then 1 else 0))) * hν

/-- A sum of products over a finite index set is a sum of r products, if r is at least the size of the index set. -/
private theorem exists_products {β γ κ : Type} [Fintype κ] {f : β → γ → ℤ} (g : κ → β → ℤ) (h : κ → γ → ℤ)
    (hf : ∀ b c, f b c = ∑ t, g t b * h t c) {r : ℕ} (hr : Fintype.card κ ≤ r) :
    ∃ (g' : Fin r → β → ℤ) (h' : Fin r → γ → ℤ), ∀ b c, f b c = ∑ t, g' t b * h' t c := by
  classical
  let e := Fintype.equivFin κ
  refine ⟨fun t b => if ht : t.1 < Fintype.card κ then g (e.symm ⟨t.1, ht⟩) b else 0,
    fun t c => if ht : t.1 < Fintype.card κ then h (e.symm ⟨t.1, ht⟩) c else 0, fun b c => ?_⟩
  rw [hf]
  refine Finset.sum_of_injOn (fun t => Fin.castLE hr (e t))
    (fun _ _ _ _ he => e.injective (Fin.castLE_injective hr he)) (fun _ _ => by simp) (fun t _ ht => ?_) (fun t _ => ?_)
  · have hlt : ¬ t.1 < Fintype.card κ := fun hlt => ht ⟨e.symm ⟨t.1, hlt⟩, by simp, by simp [Fin.castLE]⟩
    simp [hlt]
  · have hlt : (Fin.castLE hr (e t)).1 < Fintype.card κ := (e t).2
    simp only [dif_pos hlt]
    simp

section Expansion

/-! ### The coefficients: the expansion

In this section X = M₁, Y = M₂, A = F, A' = F′, B = G, B' = −G′, and l is the diagonal of D. -/

variable {p q ρ : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q] [Fintype ρ] [DecidableEq ρ]
variable {R : Type*} [CommRing R]

/-- Proof of Proposition prop:identity, the coefficients: "Up to a sign that depends on R only, the determinant of such a matrix
equals that of" the matrix with the block rows (M₁, 0, F, 0), (0, M₂, 0, G′), (0, DG, −1, 0), (DF′, 0, 0, 1) "(a Schur
complement)". Here the last two block rows are (0, −DB, 1, 0) and (−DA', 0, 0, 1), and there is no sign. -/
theorem prop_identity_schur (l : ρ → R) (X : Matrix p p R) (A : Matrix p ρ R) (A' : Matrix ρ p R)
    (Y : Matrix q q R) (B : Matrix ρ q R) (B' : Matrix q ρ R) :
    (fromBlocks X (A * diagonal l * B) (B' * diagonal l * A') Y).det =
      (fromBlocks (fromBlocks X 0 0 Y) (fromBlocks A 0 0 B')
        (-(fromBlocks 0 (diagonal l * B) (diagonal l * A') 0)) 1).det := by
  rw [det_fromBlocks_one₂₂]
  congr 1
  rw [Matrix.mul_neg, sub_neg_eq_add, fromBlocks_multiply, fromBlocks_add]
  simp [Matrix.mul_assoc]

/-- Proof of Proposition prop:identity, the coefficients: "Each of the last 2R rows is the sum of its part in DG, respectively
DF′, and its entry ±1. Expand by multilinearity, and let T₁, T₂ be the sets of rows of the third and of the fourth block row for
which the first part is taken." The term of T = (T₁, T₂) is the product of the entries of D in T, which is X^E(T) in the paper,
times the determinant of the matrix Nc.Cross.termMat T, in which the rows outside T have only their entry 1. -/
theorem prop_identity_expand (l : ρ → R) (X : Matrix p p R) (A : Matrix p ρ R) (A' : Matrix ρ p R)
    (Y : Matrix q q R) (B : Matrix ρ q R) (B' : Matrix q ρ R) :
    (fromBlocks X (A * diagonal l * B) (B' * diagonal l * A') Y).det =
      ∑ T : Finset (ρ ⊕ ρ), (∏ r ∈ T, Sum.elim l l r) * (termMat T X A A' Y B B').det := by
  have h1 : (of (Sum.elim (topRows X A Y B') fun r => Sum.elim l l r • lowRows A' B r + unitRows r) :
      Matrix ((p ⊕ q) ⊕ (ρ ⊕ ρ)) ((p ⊕ q) ⊕ (ρ ⊕ ρ)) R) =
      fromBlocks (fromBlocks X 0 0 Y) (fromBlocks A 0 0 B')
        (-(fromBlocks 0 (diagonal l * B) (diagonal l * A') 0)) 1 := by
    ext i j
    rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;>
      simp [topRows, lowRows, unitRows, Matrix.diagonal_mul]
  rw [prop_identity_schur, ← h1]
  exact det_expand (topRows X A Y B') (Sum.elim l l) (lowRows A' B) unitRows

/-- Proof of Proposition prop:identity, the coefficients: "This vanishes if |T₁| ≠ |T₂|, as the blocks are then not square". (In
Lean the rows outside T are kept, with their entry 1; the form with two blocks is Nc.Cross.termMat_eq_glue.) -/
theorem prop_identity_term_zero (T : Finset (ρ ⊕ ρ)) (hT : T.toLeft.card ≠ T.toRight.card)
    (X : Matrix p p R) (A : Matrix p ρ R) (A' : Matrix ρ p R)
    (Y : Matrix q q R) (B : Matrix ρ q R) (B' : Matrix q ρ R) :
    (termMat T X A A' Y B B').det = 0 := by
  rw [termMat_eq_glue]
  refine det_glue_zero _ _ _ _ ?_
  rw [card_cgrp]
  have := card_rgrp (p := p) (q := q) T
  omega

/-- Proof of Proposition prop:identity, the coefficients: "otherwise it is a polynomial in X depending on (s_a, s_d) times one
depending on (s_b, s_c)". For every T the determinant of the term is a function of (X, A, A') times a function of (Y, B, B'). -/
theorem prop_identity_term_product (T : Finset (ρ ⊕ ρ)) :
    ∃ (α : Matrix p p R → Matrix p ρ R → Matrix ρ p R → R)
      (β : Matrix q q R → Matrix ρ q R → Matrix q ρ R → R),
      ∀ X A A' Y B B', (termMat T X A A' Y B B').det = α X A A' * β Y B B' := by
  obtain ⟨a, b, h⟩ := det_glue (R := R) (rgrp T : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop) cgrp
  exact ⟨fun X A A' => a (termMat T X A A' 0 0 0), fun Y B B' => b (termMat T 0 0 0 Y B B'),
    fun X A A' Y B B' => by rw [termMat_eq_glue, h]⟩

/-- Proof of Proposition prop:identity, the coefficients: "The T with |T₁| = |T₂| and E(T) ≤ N are at most P(N) states". -/
theorem prop_identity_term_count (K N : ℕ) : (goodT K N).card ≤ stateCount N := by
  show (goodT K N).card ≤ (pairs N).card
  refine Finset.card_le_card_of_injOn
    (fun T => (T.toLeft.map Fin.valEmbedding, T.toRight.map Fin.valEmbedding)) ?_ ?_
  · intro T hT
    have hT' := (mem_filter.1 hT).2
    have e1 : enT T = en (T.toLeft.map Fin.valEmbedding) + en (T.toRight.map Fin.valEmbedding) := by
      conv_lhs => rw [← T.toLeft_disjSum_toRight]
      unfold enT en
      rw [Finset.sum_disjSum, Finset.sum_map, Finset.sum_map]
      rfl
    refine mem_coe.2 (mem_pairs.2 ⟨?_, ?_⟩)
    · simpa using hT'.1
    · rw [← e1]
      exact hT'.2
  · intro T _ T' _ h
    have h1 := Finset.map_injective _ (Prod.ext_iff.1 h).1
    have h2 := Finset.map_injective _ (Prod.ext_iff.1 h).2
    rw [← T.toLeft_disjSum_toRight, ← T'.toLeft_disjSum_toRight, h1, h2]

open Polynomial in
/-- Proof of Proposition prop:identity, the coefficients: "… and the degree N − E(T) can be split between the two factors in at
most N+1 ways." So the coefficient of X^N of the determinant of a matrix with the diagonal blocks X, Y and the other blocks ADB,
B'DA', D = diag(X^(2r+1)), is a sum, over the T with |T₁| = |T₂| and E(T) ≤ N and over N+1 degrees, of products of a function of
(X, A, A') and one of (Y, B, B'). -/
theorem prop_identity_near (K N : ℕ) {S T : Type*}
    (X : S → Matrix p p ℤ[X]) (A : S → Matrix p (Fin K) ℤ[X]) (A' : S → Matrix (Fin K) p ℤ[X])
    (Y : T → Matrix q q ℤ[X]) (B : T → Matrix (Fin K) q ℤ[X]) (B' : T → Matrix q (Fin K) ℤ[X]) :
    ∃ (g : ↥(goodT K N) × Fin (N + 1) → S → ℤ) (h : ↥(goodT K N) × Fin (N + 1) → T → ℤ), ∀ s t,
      (fromBlocks (X s) (A s * diagonal (fun r : Fin K => (Polynomial.X : ℤ[X]) ^ (2 * (r : ℕ) + 1)) * B t)
        (B' t * diagonal (fun r : Fin K => (Polynomial.X : ℤ[X]) ^ (2 * (r : ℕ) + 1)) * A' s) (Y t)).det.coeff N =
      ∑ k, g k s * h k t := by
  choose α β hαβ using fun T : Finset (Fin K ⊕ Fin K) => prop_identity_term_product (p := p) (q := q) (R := ℤ[X]) T
  refine ⟨fun k s => (α k.1 (X s) (A s) (A' s)).coeff k.2,
    fun k t => ((Polynomial.X : ℤ[X]) ^ (enT (k.1 : Finset (Fin K ⊕ Fin K))) *
      β k.1 (Y t) (B t) (B' t)).coeff (N - k.2), fun s t => ?_⟩
  rw [prop_identity_expand, Polynomial.finsetSum_coeff, Fintype.sum_prod_type]
  have hw : ∀ T : Finset (Fin K ⊕ Fin K),
      ∏ r ∈ T, Sum.elim (fun r : Fin K => (Polynomial.X : ℤ[X]) ^ (2 * (r : ℕ) + 1))
        (fun r : Fin K => (Polynomial.X : ℤ[X]) ^ (2 * (r : ℕ) + 1)) r = Polynomial.X ^ enT T := by
    intro T
    rw [enT, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun r _ => ?_
    rcases r with r | r <;> rfl
  rw [← Finset.sum_subset (Finset.subset_univ (goodT K N)), ← Finset.sum_coe_sort]
  · refine Finset.sum_congr rfl fun T _ => ?_
    rw [hw, hαβ, mul_left_comm, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range]
  · intro T _ hT
    rw [hw]
    by_cases hb : T.toLeft.card = T.toRight.card
    · have : N < enT T := by
        by_contra hcon
        exact hT (mem_filter.2 ⟨mem_univ _, hb, not_lt.1 hcon⟩)
      rw [Polynomial.coeff_X_pow_mul', if_neg (not_le.2 this)]
    · rw [prop_identity_term_zero T hb, mul_zero, Polynomial.coeff_zero]

end Expansion

open Polynomial in
/-- Proof of Proposition prop:identity, the coefficients: "This proves (b)": the coefficient of X^N in Ψ is a sum of at most
(N+1)P(N) products of a function of (s_a, s_d) and one of (s_b, s_c). "This is used only for the coefficients of degree at most
N < 2R", with R = N + 1. -/
theorem prop_identity_coefficients (μ ν N : ℕ) :
    ∃ (g : Fin ((N + 1) * stateCount N) → Wd μ × Wd ν → ℤ) (h : Fin ((N + 1) * stateCount N) → Wd ν × Wd μ → ℤ),
      ∀ (sa : Wd μ) (sb : Wd ν) (sc : Wd μ) (sd : Wd ν),
        (psi (Polynomial.X : ℤ[X]) sa sb sc sd).coeff N = ∑ k, g k (sa, sd) * h k (sb, sc) := by
  obtain ⟨g, h, hgh⟩ := prop_identity_near (p := Fin μ ⊕ Fin ν) (q := Fin μ ⊕ Fin ν) (N + 1) N
    (S := Wd μ × Wd ν) (T := Wd ν × Wd μ)
    (fun s => blX X s.1 s.2) (fun s => facA (N + 1) X s.1 s.2)
    (fun s => (facA (N + 1) X s.1.swap s.2.swap)ᵀ)
    (fun t => blY X t.2 t.1) (fun t => facB (N + 1) X t.2 t.1)
    (fun t => -(facB (N + 1) X t.2.swap t.1.swap)ᵀ)
  have key : ∀ (sa : Wd μ) (sb : Wd ν) (sc : Wd μ) (sd : Wd ν),
      (psi (Polynomial.X : ℤ[X]) sa sb sc sd).coeff N = ∑ k, g k (sa, sd) * h k (sb, sc) := by
    intro sa sb sc sd
    rw [← hgh, ← sub_eq_zero, ← Polynomial.coeff_sub]
    refine (Polynomial.X_pow_dvd_iff (n := 2 * (N + 1))).1 ?_ N (by omega)
    refine dvd_det_sub _ _ _ fun i j => ?_
    rcases i with i | i <;> rcases j with j | j
    · simp [matM]
    · simpa only [matM, fromBlocks_apply₁₂] using prop_identity_blocks (N + 1) X sa sd sc sb i j
    · have := prop_identity_blocks (N + 1) (X : ℤ[X]) sa.swap sd.swap sc.swap sb.swap j i
      simp only [matM, fromBlocks_apply₂₁]
      rw [← dvd_neg] at this
      convert this using 1
      have e : ∀ (A : Matrix (Fin μ ⊕ Fin ν) (Fin (N + 1)) ℤ[X]) (l : Fin (N + 1) → ℤ[X])
          (B : Matrix (Fin (N + 1)) (Fin μ ⊕ Fin ν) ℤ[X]),
          -Bᵀ * diagonal l * Aᵀ = -(A * diagonal l * B)ᵀ := by
        intro A l B
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.neg_mul,
          Matrix.neg_mul, Matrix.mul_assoc]
      rw [e]
      simp only [Matrix.neg_apply, Matrix.transpose_apply]
      ring
    · simp [matM]
  have hcard : Fintype.card (↥(goodT (N + 1) N) × Fin (N + 1)) ≤ (N + 1) * stateCount N := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (prop_identity_term_count _ _)
  obtain ⟨g', h', e⟩ := exists_products (f := fun (p : Wd μ × Wd ν) (q : Wd ν × Wd μ) =>
    (psi (Polynomial.X : ℤ[X]) p.1 q.1 q.2 p.2).coeff N) g h (fun p q => key p.1 q.1 q.2 p.2) hcard
  exact ⟨g', h', fun sa sb sc sd => e (sa, sd) (sb, sc)⟩

section reflect

open Polynomial

variable {μ ν : ℕ}

/-- The reflection identity for polynomials: the reverse of Ψ(X; s_a, s_b, s_c, s_d) is Ψ(X; s_a, s_d, s_c, s_b), up to powers
of X. -/
theorem prop_identity_reverse (sa : Wd μ) (sb : Wd ν) (sc : Wd μ) (sd : Wd ν) {e₁ e₂ : ℕ} (ha : enW sa = e₁)
    (hb : enW sb = e₂) (hc : enW sc = e₁) (hd : enW sd = e₂) :
    (psi (X : ℤ[X]) sa sb sc sd).reverse * X ^ (2 * (e₁ + e₂)) =
      psi (X : ℤ[X]) sa sd sc sb * X ^ (psi (X : ℤ[X]) sa sb sc sd).natDegree := by
  set P := psi (X : ℤ[X]) sa sb sc sd with hP
  set Q := psi (X : ℤ[X]) sa sd sc sb with hQ
  let F := FractionRing ℤ[X]
  let ι : ℤ[X] →+* F := algebraMap ℤ[X] F
  have hι : Function.Injective ι := IsFractionRing.injective ℤ[X] F
  let x : F := ι X
  have hx : x ≠ 0 := by
    intro h
    have : (X : ℤ[X]) = 0 := hι (by rw [map_zero]; exact h)
    exact X_ne_zero this
  have hxz : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  have hx1 : x ^ 2 ≠ 1 := by
    intro h
    have h1 : (X : ℤ[X]) ^ 2 = 1 := hι (by rw [map_pow, map_one]; exact h)
    have h2 := congrArg (fun p : ℤ[X] => p.coeff 2) h1
    simp [coeff_one] at h2
  have hi : ι = eval₂RingHom (Int.castRingHom F) x := by
    refine Polynomial.ringHom_ext (fun n => by simp) ?_
    simp [x]
  let φ : ℤ[X] →+* F := eval₂RingHom (Int.castRingHom F) x⁻¹
  have hφX : φ X = x⁻¹ := by simp [φ]
  let _ : Invertible (x⁻¹ : F) := ⟨x, hxz, by rw [mul_comm]; exact hxz⟩
  have hrev : ι P.reverse * (x⁻¹) ^ P.natDegree = φ P := by
    have := eval₂_reverse_mul_pow (Int.castRingHom F) (x⁻¹ : F) P
    rw [hi]
    simp only [φ, coe_eval₂RingHom]
    exact this
  have hz : psi (x⁻¹ : F) sa sb sc sd = φ P := by
    rw [hP, map_psi, hφX]
  have hxQ : psi x sa sd sc sb = ι Q := by
    rw [hQ, map_psi]
  have key := prop_identity_reflection hxz hx1 sa sb sc sd ha hb hc hd
  rw [hz, hxQ, ← hrev] at key
  apply hι
  rw [map_mul, map_mul, map_pow, map_pow, ← key]
  show ι P.reverse * x ^ _ = _ * x ^ _
  have : (x⁻¹) ^ P.natDegree * x ^ P.natDegree = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hx, one_pow]
  linear_combination (-(ι P.reverse * x ^ (2 * (e₁ + e₂)))) * this

/-- Proof of Proposition prop:identity, reflection: "Hence deg Ψ ≤ Θ, and the coefficient of X^N at (s_a, s_b, s_c, s_d) is that
of X^(Θ−N) at (s_a, s_d, s_c, s_b)." -/
theorem prop_identity_reflection_coeff (sa : Wd μ) (sb : Wd ν) (sc : Wd μ) (sd : Wd ν) {e₁ e₂ : ℕ} (ha : enW sa = e₁)
    (hb : enW sb = e₂) (hc : enW sc = e₁) (hd : enW sd = e₂) :
    (psi (X : ℤ[X]) sa sb sc sd).natDegree ≤ 2 * (e₁ + e₂) ∧
    ∀ N M, N + M = 2 * (e₁ + e₂) →
      (psi (X : ℤ[X]) sa sb sc sd).coeff N = (psi (X : ℤ[X]) sa sd sc sb).coeff M := by
  have key := prop_identity_reverse sa sb sc sd ha hb hc hd
  set P := psi (X : ℤ[X]) sa sb sc sd with hP
  set Q := psi (X : ℤ[X]) sa sd sc sb with hQ
  set H := 2 * (e₁ + e₂) with hH
  have hdeg : P.natDegree ≤ H := by
    by_contra hcon
    have h1 := congrArg (fun p : ℤ[X] => p.coeff H) key
    simp only [coeff_mul_X_pow', le_refl, if_true, Nat.sub_self, hcon, if_false, coeff_zero_reverse,
      leadingCoeff_eq_zero] at h1
    rw [h1] at hcon
    simp at hcon
  refine ⟨hdeg, fun N M hNM => ?_⟩
  rcases le_or_gt N P.natDegree with hN | hN
  · have h1 := congrArg (fun p : ℤ[X] => p.coeff (H + (P.natDegree - N))) key
    simp only [coeff_mul_X_pow', Nat.le_add_right, if_true, Nat.add_sub_cancel_left] at h1
    rw [if_pos (by omega), coeff_reverse, revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hN] at h1
    rw [h1]
    congr 1
    omega
  · rw [coeff_eq_zero_of_natDegree_lt hN]
    have h1 := congrArg (fun p : ℤ[X] => p.coeff (M + P.natDegree)) key
    simp only [coeff_mul_X_pow', Nat.le_add_left, if_true, Nat.add_sub_cancel] at h1
    rw [if_neg (by omega)] at h1
    exact h1

end reflect

/-- **Paper: Proposition prop:identity.** "Let Θ = 2(e₁+e₂). There are integral tensors Ψ_0, …, Ψ_Θ such that, all functions
below being integer valued, (a) ∑_N Ψ_N is ⟨|Σ₁|⟩_ac ⟨|Σ₂|⟩_bd; (b) Ψ_N is a sum of at most (N+1)P(N) products of a function of
(s_a, s_d) and one of (s_b, s_c); (c) Ψ_N is a sum of at most (N′+1)P(N′) products of a function of (s_a, s_b) and one of
(s_c, s_d), where N′ = Θ − N." -/
theorem prop_identity (μ ν e₁ e₂ : ℕ) :
    ∃ Ψ : Fin (2 * (e₁ + e₂) + 1) → ↥(states μ e₁) → ↥(states ν e₂) → ↥(states μ e₁) → ↥(states ν e₂) → ℤ,
      (∀ a b c d, ∑ N, Ψ N a b c d = (if a = c then 1 else 0) * (if b = d then 1 else 0)) ∧
      (∀ N : Fin (2 * (e₁ + e₂) + 1), ∃ (g : Fin ((N.1 + 1) * stateCount N) → ↥(states μ e₁) × ↥(states ν e₂) → ℤ)
        (h : Fin ((N.1 + 1) * stateCount N) → ↥(states ν e₂) × ↥(states μ e₁) → ℤ),
        ∀ a b c d, Ψ N a b c d = ∑ k, g k (a, d) * h k (b, c)) ∧
      (∀ N : Fin (2 * (e₁ + e₂) + 1), ∀ N', N' = 2 * (e₁ + e₂) - N.1 →
        ∃ (g : Fin ((N' + 1) * stateCount N') → ↥(states μ e₁) × ↥(states ν e₂) → ℤ)
        (h : Fin ((N' + 1) * stateCount N') → ↥(states μ e₁) × ↥(states ν e₂) → ℤ),
        ∀ a b c d, Ψ N a b c d = ∑ k, g k (a, b) * h k (c, d)) := by
  obtain ⟨ε, hε⟩ := prop_identity_one μ ν
  have hεε : ((ε : ℤˣ) : ℤ) * ε = 1 := Int.units_coe_mul_self ε
  have hrefl := fun (a : ↥(states μ e₁)) (b : ↥(states ν e₂)) (c : ↥(states μ e₁)) (d : ↥(states ν e₂)) =>
    prop_identity_reflection_coeff (word a) (word b) (word c).swap (word d).swap (enW_word a) (enW_word b)
      ((enW_swap _).trans (enW_word c)) ((enW_swap _).trans (enW_word d))
  refine ⟨fun N a b c d => ε * (psi (Polynomial.X : Polynomial ℤ) (word a) (word b) (word c).swap
    (word d).swap).coeff N, fun a b c d => ?_, fun N => ?_, fun N N' hN' => ?_⟩
  · rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun N => (psi (Polynomial.X : Polynomial ℤ) (word a)
      (word b) (word c).swap (word d).swap).coeff N)]
    have h1 := Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hrefl a b c d).1) 1
    simp only [one_pow, mul_one] at h1
    rw [← Nat.succ_eq_add_one, ← h1, ← Polynomial.coe_evalRingHom, map_psi, Polynomial.coe_evalRingHom,
      Polynomial.eval_X, hε _ _ _ _ (word_strictMono a).1 (word_strictMono a).2 (word_strictMono b).1
      (word_strictMono b).2 (word_strictMono c).2 (word_strictMono c).1 (word_strictMono d).2
      (word_strictMono d).1, ← mul_assoc, hεε, one_mul, Prod.swap_swap, Prod.swap_swap]
    simp only [word_injective.eq_iff]
    rw [ite_and]
    split_ifs <;> simp only [mul_one, mul_zero]
  · obtain ⟨g, h, hgh⟩ := prop_identity_coefficients μ ν N
    refine ⟨fun k p => ε * g k (word p.1, (word p.2).swap), fun k p => h k (word p.1, (word p.2).swap),
      fun a b c d => ?_⟩
    simp only
    rw [hgh, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · subst hN'
    obtain ⟨g, h, hgh⟩ := prop_identity_coefficients μ ν (2 * (e₁ + e₂) - N)
    refine ⟨fun k p => ε * g k (word p.1, word p.2), fun k p => h k ((word p.2).swap, (word p.1).swap),
      fun a b c d => ?_⟩
    simp only
    rw [(hrefl a b c d).2 N (2 * (e₁ + e₂) - N) (by omega), hgh, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

end Paper
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Estimates for the crossing inequality

For Paper.prop_crossing_class_size, prop_crossing_products and prop_crossing_tensors (Paper/Crossing.lean): logarithms are small
against square roots, and the number of states of energy about p²n.
-/

namespace Nc.Cross

open Finset Filter

theorem log_small {A : ℝ} (hA : 0 ≤ A) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, Real.log (A * n + 1) ≤ η * Real.sqrt n := by
  have h1 : (fun x : ℝ => Real.log x) =o[atTop] fun x => x ^ (1 / 2 : ℝ) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have h2 := tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually (h1.bound (half_pos hη))
  have h3 : ∀ᶠ n : ℕ in atTop, Real.log (A + 1) / (η / 2) ≤ Real.sqrt n :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop _
  filter_upwards [h2, h3, eventually_ge_atTop 1] with n h2 h3 hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [div_le_iff₀ (half_pos hη)] at h3
  rw [← Real.sqrt_eq_rpow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h2
  have h4 := (le_abs_self _).trans h2
  calc Real.log (A * n + 1) ≤ Real.log ((A + 1) * n) := Real.log_le_log (by positivity) (by nlinarith)
    _ = Real.log (A + 1) + Real.log n := Real.log_mul (by positivity) (by positivity)
    _ ≤ _ := by linarith

theorem floor_le' {p : ℝ} (n : ℕ) : ((⌊p ^ 2 * n⌋₊ : ℕ) : ℝ) ≤ p ^ 2 * n := Nat.floor_le (by positivity)

theorem sqrt_floor_le {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    Real.sqrt (⌊p ^ 2 * n⌋₊ : ℕ) ≤ p * Real.sqrt n := by
  rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact floor_le' n

theorem lower_bound {c : ℝ} (hc : 0 < c)
    (hl : ∀ ε > 0, ∃ E₀ : ℕ, ∀ E, E₀ ≤ E → (c - ε) * Real.sqrt E ≤ lp E) {p : ℝ} (hp : 0 ≤ p)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, c * p * Real.sqrt n - η * Real.sqrt n ≤
      lp ⌊p ^ 2 * n⌋₊ - 2 * Real.log ((⌊p ^ 2 * n⌋₊ : ℕ) + 1) := by
  rcases hp.eq_or_lt with rfl | hp
  · refine Eventually.of_forall fun n => ?_
    have : 0 ≤ η * Real.sqrt n := by positivity
    simp [lp_zero, this]
  set ε : ℝ := min (η / (4 * (p + 1))) c with hε
  have hε0 : 0 < ε := lt_min (by positivity) hc
  have hεc : ε ≤ c := min_le_right _ _
  have hεp : ε * p ≤ η / 4 := by
    have h1 : ε ≤ η / (4 * (p + 1)) := min_le_left _ _
    calc ε * p ≤ η / (4 * (p + 1)) * p := mul_le_mul_of_nonneg_right h1 hp.le
      _ ≤ η / (4 * (p + 1)) * (p + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = η / 4 := by field_simp
  obtain ⟨E₀, hE₀⟩ := hl ε hε0
  have a1 := log_small (A := p ^ 2) (by positivity) (η := η / 8) (by positivity)
  have hsq := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have a2 : ∀ᶠ n : ℕ in atTop, 1 / p ≤ Real.sqrt n := hsq.eventually_ge_atTop _
  have a3 : ∀ᶠ n : ℕ in atTop, c / (η / 4) ≤ Real.sqrt n := hsq.eventually_ge_atTop _
  have a4 : ∀ᶠ n : ℕ in atTop, (E₀ : ℝ) / p ^ 2 ≤ n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  filter_upwards [a1, a2, a3, a4] with n a1 a2 a3 a4
  set E := ⌊p ^ 2 * n⌋₊ with hE
  have hp2 : 0 < p ^ 2 := by positivity
  rw [div_le_iff₀ hp] at a2
  rw [div_le_iff₀ (by positivity)] at a3
  rw [div_le_iff₀ hp2] at a4
  have b1 : E₀ ≤ E := Nat.le_floor (by linarith)
  have b2 := hE₀ E b1
  have b3 : p ^ 2 * n - 1 ≤ E := by
    have := Nat.lt_floor_add_one (p ^ 2 * (n : ℝ))
    linarith
  have b4 : p * Real.sqrt n - 1 ≤ Real.sqrt E := by
    refine Real.le_sqrt_of_sq_le ?_
    have : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
    nlinarith
  have b5 : Real.log ((E : ℝ) + 1) ≤ η / 8 * Real.sqrt n :=
    (Real.log_le_log (by positivity) (by linarith [floor_le' (p := p) n])).trans a1
  have b6 : (c - ε) * (p * Real.sqrt n - 1) ≤ (c - ε) * Real.sqrt E :=
    mul_le_mul_of_nonneg_left b4 (by linarith)
  have b7 : ε * p * Real.sqrt n ≤ η / 4 * Real.sqrt n :=
    mul_le_mul_of_nonneg_right hεp (Real.sqrt_nonneg _)
  nlinarith

end Nc.Cross
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Restrictions and sums of restrictions: the basic calculus

Paper: the subsection "Tensors". `Restr s t` says that s is a restriction of t, and `SumRestr s b` that s
is covered by the b k. Restriction is reflexive and
transitive and compatible with products, powers, products of families and `push` (giving legs to
parties); sums of restrictions can be substituted in one another and multiplied, and are compatible
with the same operations.
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-! ### Values of the constructions -/

@[simp] theorem one_val (x : ∀ p, (1 : Ten K I).ι p) : (1 : Ten K I).val x = 1 := rfl

theorem mul_val (s t : Ten K I) (x : ∀ p, (s * t).ι p) :
    (s * t).val x = s.val (fun p => (x p).1) * t.val (fun p => (x p).2) := rfl

theorem prod_val {κ : Type} [Fintype κ] [DecidableEq κ] (b : κ → Ten K I)
    (x : ∀ p, (prod b).ι p) : (prod b).val x = ∏ k, (b k).val (fun p => x p k) := rfl

theorem push_val (π : J → I) (t : Ten K J) (x : ∀ q, (push π t).ι q) :
    (push π t).val x = t.val (fun j => x (π j) ⟨j, rfl⟩) := rfl

theorem unit_val (r : ℕ) (x : J → Fin r) :
    (unit K J r).val x = if ∀ i j, x i = x j then 1 else 0 := rfl

/-- The k-th power is the product of k equal tensors. -/
theorem kpow_eq_prod (t : Ten K I) (k : ℕ) : kpow t k = prod (fun _ : Fin k => t) := rfl

/-- The same legs with another array. -/
def withVal (t : Ten K I) (v : (∀ p, t.ι p) → K) : Ten K I where
  ι := t.ι
  val := v

@[simp] theorem withVal_val (t : Ten K I) (v : (∀ p, t.ι p) → K) : (t.withVal v).val = v := rfl

/-! ### Local maps applied to arrays -/

/-- Local maps L applied to an array f; this is `app` for plain index sets in the place of the legs of
tensors. -/
def appG {α β : I → Type} [∀ p, Fintype (β p)] (L : ∀ p, α p → β p → K)
    (f : (∀ p, β p) → K) (x : ∀ p, α p) : K :=
  ∑ y, (∏ p, L p (x p) (y p)) * f y

theorem app_eq_appG {s t : Ten K I} (L : Loc s t) (x : ∀ p, s.ι p) : app L x = appG L t.val x := rfl

/-- Local maps compose. -/
theorem appG_comp {α β γ : I → Type} [∀ p, Fintype (β p)] [∀ p, Fintype (γ p)]
    (L : ∀ p, α p → β p → K) (M : ∀ p, β p → γ p → K) (f : (∀ p, γ p) → K) (x : ∀ p, α p) :
    appG L (appG M f) x = appG (fun p a c => ∑ b, L p a b * M p b c) f x := by
  simp only [appG, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Fintype.prod_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]

/-- Local maps applied to a sum. -/
theorem appG_sum {α β : I → Type} [∀ p, Fintype (β p)] {κ : Type} [Fintype κ]
    (L : ∀ p, α p → β p → K) (f : κ → (∀ p, β p) → K) (x : ∀ p, α p) :
    appG L (fun y => ∑ k, f k y) x = ∑ k, appG L (f k) x := by
  simp only [appG, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Local maps applied to a product of two arrays. -/
theorem appG_mul {α β α' β' : I → Type} [∀ p, Fintype (β p)] [∀ p, Fintype (β' p)]
    (L : ∀ p, α p → β p → K) (L' : ∀ p, α' p → β' p → K)
    (f : (∀ p, β p) → K) (g : (∀ p, β' p) → K) (x : ∀ p, α p × α' p) :
    appG (β := fun p => β p × β' p) (fun p a b => L p a.1 b.1 * L' p a.2 b.2)
      (fun y => f (fun p => (y p).1) * g (fun p => (y p).2)) x =
    appG L f (fun p => (x p).1) * appG L' g (fun p => (x p).2) := by
  simp only [appG]
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    ⟨fun y => (fun p => (y p).1, fun p => (y p).2), fun z p => (z.1 p, z.2 p),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun y => ?_
  simp only [Equiv.coe_fn_mk, Finset.prod_mul_distrib]
  ring

/-- Local maps applied to a product of a family of arrays. -/
theorem appG_prod {κ : Type} [Fintype κ] [DecidableEq κ] {α β : κ → I → Type}
    [∀ k p, Fintype (β k p)] (L : ∀ k p, α k p → β k p → K) (f : ∀ k, (∀ p, β k p) → K)
    (x : ∀ p k, α k p) :
    appG (β := fun p => ∀ k, β k p) (fun p a b => ∏ k, L k p (a k) (b k))
      (fun y => ∏ k, f k (fun p => y p k)) x =
    ∏ k, appG (L k) (f k) (fun p => x p k) := by
  simp only [appG]
  rw [Fintype.prod_sum]
  refine Fintype.sum_equiv (Equiv.piComm _) _ _ fun y => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_comm]
  rfl

/-- The index tuples of the legs sorted by their parties correspond to the index tuples of all
legs. -/
def pushEquiv (π : J → I) (β : J → Type) :
    (∀ q, ∀ j : {j : J // π j = q}, β j.1) ≃ (∀ j, β j) where
  toFun y j := y (π j) ⟨j, rfl⟩
  invFun z _ j := z j.1
  left_inv y := by
    funext q j
    obtain ⟨j, rfl⟩ := j
    rfl
  right_inv _ := rfl

/-- Local maps applied to an array whose legs are sorted by parties. -/
theorem appG_push (π : J → I) {α β : J → Type} [∀ j, Fintype (β j)]
    (L : ∀ j, α j → β j → K) (f : (∀ j, β j) → K) (x : ∀ q, ∀ j : {j : J // π j = q}, α j.1) :
    appG (β := fun q => ∀ j : {j : J // π j = q}, β j.1)
      (fun q a b => ∏ j : {j : J // π j = q}, L j.1 (a j) (b j))
      (fun y => f (fun j => y (π j) ⟨j, rfl⟩)) x =
    appG L f (fun j => x (π j) ⟨j, rfl⟩) := by
  simp only [appG]
  refine Fintype.sum_equiv (pushEquiv π β) _ _ fun y => ?_
  congr 1
  rw [← Fintype.prod_fiberwise π]
  refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun j _ => ?_
  obtain ⟨j, rfl⟩ := j
  rfl

/-- Local maps whose matrices have at most one entry that is not 0 in each row: the row a of the
matrix of p has the entry w p a in the column g p a. -/
theorem appG_map {α β : I → Type} [∀ p, Fintype (β p)] [∀ p, DecidableEq (β p)]
    (w : ∀ p, α p → K) (g : ∀ p, α p → β p) (f : (∀ p, β p) → K) (x : ∀ p, α p) :
    appG (fun p a b => if b = g p a then w p a else 0) f x =
      (∏ p, w p (x p)) * f (fun p => g p (x p)) := by
  unfold appG
  rw [Finset.sum_eq_single (fun p => g p (x p))]
  · simp
  · intro y _ hy
    obtain ⟨p, hp⟩ := Function.ne_iff.1 hy
    rw [Finset.prod_eq_zero (Finset.mem_univ p), zero_mul]
    exact if_neg hp
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### Restrictions -/

/-- A tensor is a restriction of itself. -/
theorem Restr.refl (t : Ten K I) : Restr t t :=
  ⟨fun _ a b => if b = a then 1 else 0, fun x => by
    rw [app_eq_appG]
    exact ((appG_map (fun p _ => (1 : K)) (fun p a => a) t.val x).trans (by simp)).symm⟩

/-- A restriction of a restriction is a restriction. -/
theorem Restr.trans {s t u : Ten K I} (h : Restr s t) (h' : Restr t u) : Restr s u := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := h'
  refine ⟨fun p a c => ∑ b, L p a b * M p b c, fun x => ?_⟩
  rw [hL, app_eq_appG, app_eq_appG, ← appG_comp]
  congr 1
  funext y
  exact hM y

/-- Products of restrictions. -/
theorem Restr.mul {s t s' t' : Ten K I} (h : Restr s s') (h' : Restr t t') :
    Restr (s * t) (s' * t') := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := h'
  refine ⟨fun p a b => L p a.1 b.1 * M p a.2 b.2, fun x => ?_⟩
  rw [mul_val, hL, hM]
  exact (appG_mul L M s'.val t'.val x).symm

/-- Products of a family of restrictions. -/
theorem Restr.prod {κ : Type} [Fintype κ] [DecidableEq κ] {a b : κ → Ten K I}
    (h : ∀ k, Restr (a k) (b k)) : Restr (Ten.prod a) (Ten.prod b) := by
  choose L hL using h
  refine ⟨fun p x y => ∏ k, L k p (x k) (y k), fun x => ?_⟩
  rw [prod_val]
  exact (Finset.prod_congr rfl fun k _ => hL k _).trans
    (appG_prod (α := fun k p => (a k).ι p) (β := fun k p => (b k).ι p) L
      (fun k => (b k).val) x).symm

/-- Restrictions stay restrictions if the legs are given to other parties. -/
theorem Restr.push (π : J → I) {s t : Ten K J} (h : Restr s t) :
    Restr (push π s) (push π t) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨fun q a b => ∏ j : {j : J // π j = q}, L j.1 (a j) (b j), fun x => ?_⟩
  rw [push_val, hL]
  exact (appG_push π L t.val x).symm

/-- If the entry of s at x is a product of local factors times the entry of t at g(x), where g acts
leg by leg, then s is a restriction of t. -/
theorem Restr.of_map {s t : Ten K I} (w : ∀ p, s.ι p → K) (g : ∀ p, s.ι p → t.ι p)
    (h : ∀ x, s.val x = (∏ p, w p (x p)) * t.val (fun p => g p (x p))) : Restr s t :=
  ⟨fun p a b => if b = g p a then w p a else 0, fun x => by
    rw [h, app_eq_appG]; exact (appG_map w g t.val x).symm⟩

/-- If the entry of s at x is the entry of t at g(x), where g acts leg by leg, then s is a
restriction of t. -/
theorem Restr.of_map' {s t : Ten K I} (g : ∀ p, s.ι p → t.ι p)
    (h : ∀ x, s.val x = t.val (fun p => g p (x p))) : Restr s t :=
  Restr.of_map (fun _ _ => 1) g (by simpa using h)

/-- 1 is a restriction of every tensor with an entry that is not 0, if there is a party. -/
theorem Restr.one_le [Nonempty I] {t : Ten K I} {y : ∀ p, t.ι p} (h : t.val y ≠ 0) :
    Restr 1 t := by
  classical
  let p₀ : I := Classical.arbitrary I
  refine Restr.of_map (fun p _ => if p = p₀ then (t.val y)⁻¹ else 1) (fun p _ => y p) fun x => ?_
  rw [Finset.prod_ite_eq' Finset.univ p₀]
  simp [h]

/-! ### Sums of restrictions -/

section Sum

variable {κ κ' : Type} [Fintype κ] [Fintype κ']

/-- s is a sum of restrictions of the b k if and only if its array is a sum of arrays, the k-th
of which is a restriction of b k. -/
theorem sumRestr_iff {s : Ten K I} {b : κ → Ten K I} :
    SumRestr s b ↔ ∃ v : κ → (∀ p, s.ι p) → K,
      (∀ x, s.val x = ∑ k, v k x) ∧ ∀ k, Restr (s.withVal (v k)) (b k) := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨fun k x => appG (L k) (b k).val x, hL, fun k => ⟨L k, fun x => rfl⟩⟩
  · rintro ⟨v, hv, h⟩
    choose L hL using h
    exact ⟨L, fun x => (hv x).trans (Finset.sum_congr rfl fun k _ => hL k x)⟩

/-- If the array of s is the sum of the arrays v k, then s is a sum of restrictions of the tensors
with these arrays. -/
theorem SumRestr.of_withVal (s : Ten K I) (v : κ → (∀ p, s.ι p) → K)
    (h : ∀ x, s.val x = ∑ k, v k x) : SumRestr s (fun k => s.withVal (v k)) :=
  sumRestr_iff.2 ⟨v, h, fun _ => Restr.refl _⟩

/-- A restriction is a sum of restrictions with one term. -/
theorem Restr.sumRestr {s t : Ten K I} (h : Restr s t) : SumRestr s (fun _ : Unit => t) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨fun _ => L, fun x => by simpa using hL x⟩

/-- A tensor whose array is 0 is a sum of restrictions of the empty family. -/
theorem SumRestr.of_zero [IsEmpty κ] {s : Ten K I} (h : ∀ x, s.val x = 0) (b : κ → Ten K I) :
    SumRestr s b :=
  ⟨fun k => isEmptyElim k, fun x => by simp [h]⟩

/-- A sum of restrictions of tensors that are themselves sums of restrictions is a sum of restrictions
(covers are transitive). -/
theorem SumRestr.bind {μ : κ → Type} [∀ k, Fintype (μ k)] {s : Ten K I} {b : κ → Ten K I}
    {c : ∀ k, μ k → Ten K I} (h : SumRestr s b) (h' : ∀ k, SumRestr (b k) (c k)) :
    SumRestr s (fun x : Σ k, μ k => c x.1 x.2) := by
  obtain ⟨L, hL⟩ := h
  choose M hM using h'
  refine ⟨fun x p a d => ∑ b, L x.1 p a b * M x.1 x.2 p b d, fun x => ?_⟩
  rw [hL, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (b k).val = fun y => ∑ m, appG (M k m) (c k m).val y := funext fun y => hM k y
  rw [app_eq_appG, e, appG_sum]
  exact Finset.sum_congr rfl fun m _ => appG_comp _ _ _ _

/-- A restriction of a sum of restrictions is a sum of restrictions of the same tensors. -/
theorem Restr.trans_sum {s t : Ten K I} {b : κ → Ten K I} (h : Restr s t) (h' : SumRestr t b) :
    SumRestr s b := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := h'
  refine ⟨fun k p a d => ∑ b, L p a b * M k p b d, fun x => ?_⟩
  have e : t.val = fun y => ∑ k, appG (M k) (b k).val y := funext fun y => hM y
  rw [hL, app_eq_appG, e, appG_sum]
  exact Finset.sum_congr rfl fun m _ => appG_comp _ _ _ _

/-- In a sum of restrictions every term may be replaced by a tensor of which it is a restriction. -/
theorem SumRestr.mono {s : Ten K I} {b c : κ → Ten K I} (h : SumRestr s b)
    (h' : ∀ k, Restr (b k) (c k)) : SumRestr s c := by
  obtain ⟨v, hv, h⟩ := sumRestr_iff.1 h
  exact sumRestr_iff.2 ⟨v, hv, fun k => (h k).trans (h' k)⟩

/-- The terms of a sum of restrictions may be renamed. -/
theorem SumRestr.reindex {s : Ten K I} {b : κ → Ten K I} (h : SumRestr s b) (e : κ' ≃ κ) :
    SumRestr s (fun k => b (e k)) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨fun k => L (e k), fun x => (hL x).trans (Fintype.sum_equiv e _ _ fun _ => rfl).symm⟩

/-- The product of two sums of restrictions is a sum of restrictions of the products of two terms. -/
theorem SumRestr.mul {s t : Ten K I} {b : κ → Ten K I} {c : κ' → Ten K I} (h : SumRestr s b)
    (h' : SumRestr t c) : SumRestr (s * t) (fun k : κ × κ' => b k.1 * c k.2) := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := h'
  refine ⟨fun k p x y => L k.1 p x.1 y.1 * M k.2 p x.2 y.2, fun x => ?_⟩
  rw [mul_val, hL, hM, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Finset.sum_congr rfl fun k _ => (appG_mul (L k.1) (M k.2) (b k.1).val (c k.2).val x).symm

/-- A sum of restrictions stays one if the legs are given to other parties. -/
theorem SumRestr.push (π : J → I) {s : Ten K J} {b : κ → Ten K J} (h : SumRestr s b) :
    SumRestr (push π s) (fun k => Ten.push π (b k)) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨fun k q x y => ∏ j : {j : J // π j = q}, L k j.1 (x j) (y j), fun x => ?_⟩
  rw [push_val, hL]
  exact Finset.sum_congr rfl fun k _ => (appG_push π (L k) (b k).val x).symm

end Sum

end Ten

end Ov
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Equivalence of tensors

The paper identifies tensors that are restrictions of one another (in the subsection "Tensors"). Here they are called equivalent, `Equi`, and this file has the laws of products,
powers, products of families and `push` (giving legs to parties) up to equivalence.
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Every tensor is equivalent to itself. -/
theorem Equi.refl (t : Ten K I) : Equi t t := ⟨Restr.refl t, Restr.refl t⟩

/-- Equivalence is symmetric. -/
theorem Equi.symm {s t : Ten K I} (h : Equi s t) : Equi t s := ⟨h.2, h.1⟩

/-- Equivalence is transitive. -/
theorem Equi.trans {s t u : Ten K I} (h : Equi s t) (h' : Equi t u) : Equi s u :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-- Products of equivalent tensors are equivalent. -/
theorem Equi.mul {s t s' t' : Ten K I} (h : Equi s s') (h' : Equi t t') :
    Equi (s * t) (s' * t') := ⟨h.1.mul h'.1, h.2.mul h'.2⟩

/-- Giving the legs of equivalent tensors to parties. -/
theorem Equi.push (π : J → I) {s t : Ten K J} (h : Equi s t) :
    Equi (push π s) (push π t) := ⟨h.1.push π, h.2.push π⟩

/-- Tensors whose index sets correspond to one another, leg by leg, with equal entries are
equivalent. -/
theorem Equi.of_equiv {s t : Ten K I} (e : ∀ p, s.ι p ≃ t.ι p)
    (h : ∀ x, s.val x = t.val (fun p => e p (x p))) : Equi s t :=
  ⟨Restr.of_map' (fun p => e p) h, Restr.of_map' (fun p => (e p).symm) fun y => by
    rw [h]; simp⟩

/-! ### Products -/

/-- The product is commutative. -/
theorem Equi.mul_comm (s t : Ten K I) : Equi (s * t) (t * s) :=
  Equi.of_equiv (fun _ => Equiv.prodComm _ _) fun _ => _root_.mul_comm _ _

/-- The product is associative. -/
theorem Equi.mul_assoc (s t u : Ten K I) : Equi (s * t * u) (s * (t * u)) :=
  Equi.of_equiv (fun _ => Equiv.prodAssoc _ _ _) fun _ => _root_.mul_assoc _ _ _

/-- 1 is neutral. -/
theorem Equi.one_mul (t : Ten K I) : Equi (1 * t) t :=
  Equi.of_equiv (fun p => Equiv.punitProd (t.ι p)) fun _ => _root_.one_mul _

/-- 1 is neutral. -/
theorem Equi.mul_one (t : Ten K I) : Equi (t * 1) t :=
  Equi.of_equiv (fun p => Equiv.prodPUnit (t.ι p)) fun _ => _root_.mul_one _

section Prod

variable {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

/-- Renaming the factors of a product. -/
theorem Equi.prod_reindex (b : κ → Ten K I) (e : κ' ≃ κ) :
    Equi (Ten.prod b) (Ten.prod fun k => b (e k)) :=
  Equi.symm <| Equi.of_equiv (fun p => Equiv.piCongrLeft (fun k => (b k).ι p) e) fun x => by
    rw [prod_val, prod_val]
    refine Fintype.prod_equiv e _ _ fun k => ?_
    congr 1
    funext p
    exact (Equiv.piCongrLeft_apply_apply (fun k => (b k).ι p) e (x p) k).symm

/-- The product of the empty family. -/
theorem Equi.prod_empty [IsEmpty κ] (b : κ → Ten K I) : Equi (Ten.prod b) 1 :=
  Equi.of_equiv (fun p => show (∀ k, (b k).ι p) ≃ Unit from Equiv.equivPUnit _)
    fun x => by rw [prod_val]; simp

/-- The product of a family with one member. -/
theorem Equi.prod_unique [Unique κ] (b : κ → Ten K I) : Equi (Ten.prod b) (b default) :=
  Equi.of_equiv (fun p => show (∀ k, (b k).ι p) ≃ (b default).ι p from Equiv.piUnique _)
    fun x => by rw [prod_val]; simp; rfl

/-- The product over a disjoint union. -/
theorem Equi.prod_sum (b : κ ⊕ κ' → Ten K I) :
    Equi (Ten.prod b) (Ten.prod (fun k => b (Sum.inl k)) * Ten.prod (fun k => b (Sum.inr k))) :=
  Equi.of_equiv (fun p => Equiv.sumPiEquivProdPi fun k => (b k).ι p)
    fun x => by rw [prod_val, Fintype.prod_sum_type]; rfl

end Prod

/-- The product of a family indexed by 0, …, n is its first member times the product of the others. -/
theorem Equi.prod_fin_succ {n : ℕ} (b : Fin (n + 1) → Ten K I) :
    Equi (Ten.prod b) (b 0 * Ten.prod fun k : Fin n => b k.succ) :=
  Equi.of_equiv (fun p => (Fin.consEquiv fun k => (b k).ι p).symm)
    fun x => by rw [prod_val, Fin.prod_univ_succ]; rfl

/-- The product of a family of two tensors. -/
theorem Equi.prod_fin_two (b : Fin 2 → Ten K I) : Equi (Ten.prod b) (b 0 * b 1) :=
  (Equi.prod_fin_succ b).trans ((Equi.refl _).mul (Equi.prod_unique _))

/-! ### Powers -/

/-- The power with exponent 0. -/
theorem Equi.kpow_zero (t : Ten K I) : Equi (Ten.kpow t 0) 1 :=
  Equi.prod_empty (fun _ : Fin 0 => t)

/-- The power with exponent k + 1. -/
theorem Equi.kpow_succ (t : Ten K I) (k : ℕ) : Equi (Ten.kpow t (k + 1)) (t * Ten.kpow t k) :=
  Equi.prod_fin_succ (fun _ : Fin (k + 1) => t)

/-! ### Giving legs to parties -/

section Push

variable {L : Type} [Fintype L] [DecidableEq L]

/-- Giving each leg to the party of its own name changes nothing, up to equivalence. -/
theorem Equi.push_id (t : Ten K I) : Equi (Ten.push id t) t :=
  Equi.of_equiv
    (fun q => ⟨fun y => y ⟨q, rfl⟩, fun a j => (show q = j.1 from j.2.symm) ▸ a, fun y => by
        funext j; obtain ⟨j, hj⟩ := j; cases hj; rfl, fun a => rfl⟩)
    fun x => rfl

/-- Giving legs away twice. -/
theorem Equi.push_push (π : J → I) (ρ : L → J) (t : Ten K L) :
    Equi (Ten.push π (Ten.push ρ t)) (Ten.push (π ∘ ρ) t) :=
  Equi.of_equiv
    (fun q => ⟨fun y i => y ⟨ρ i.1, i.2⟩ ⟨i.1, rfl⟩, fun z j i => z ⟨i.1, by
        rw [Function.comp, i.2]; exact j.2⟩, fun y => by
        funext j i
        obtain ⟨j, hj⟩ := j
        obtain ⟨i, hi⟩ := i
        cases hj
        cases hi
        rfl, fun _ => rfl⟩)
    fun _ => rfl

/-- Giving legs away, for a product. -/
theorem Equi.push_mul (π : J → I) (s t : Ten K J) :
    Equi (Ten.push π (s * t)) (Ten.push π s * Ten.push π t) :=
  Equi.of_equiv
    (fun _ => ⟨fun y => (fun j => (y j).1, fun j => (y j).2), fun z j => (z.1 j, z.2 j),
      fun _ => rfl, fun _ => rfl⟩)
    fun _ => rfl

/-- Giving legs away, for 1. -/
theorem Equi.push_one (π : J → I) : Equi (Ten.push π (1 : Ten K J)) 1 :=
  Equi.of_equiv
    (fun q => show (({j : J // π j = q}) → Unit) ≃ Unit from Equiv.equivPUnit _) fun _ => rfl

/-- Giving legs away, for the product of a family. -/
theorem Equi.push_prod {κ : Type} [Fintype κ] [DecidableEq κ] (π : J → I) (b : κ → Ten K J) :
    Equi (Ten.push π (Ten.prod b)) (Ten.prod fun k => Ten.push π (b k)) :=
  Equi.of_equiv (fun _ => Equiv.piComm _) fun _ => rfl

/-- Giving legs away, for a power. -/
theorem Equi.push_kpow (π : J → I) (t : Ten K J) (k : ℕ) :
    Equi (Ten.push π (Ten.kpow t k)) (Ten.kpow (Ten.push π t) k) :=
  Equi.push_prod π (fun _ : Fin k => t)

end Push

end Ten

end Ov
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Spectral points: the basic calculus

Paper: the subsection "Tensors". A spectral point F is multiplicative and
monotone for restriction, F(s) ≤ F(t_1) + … + F(t_m) if s = t_1 + … + t_m, and 1 ≤ F(t) ≤ rank of t for
a tensor t that is not 0. A spectral point can be pulled back along a map g of sets of parties (the
paper's t ↦ φ(gt)).
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Rank, in coordinates: a tensor has rank at most r if and only if it is a sum of r products of
vectors. -/
theorem rankLE_iff [Nonempty I] {t : Ten K I} {r : ℕ} :
    RankLE t r ↔ ∃ u : Fin r → ∀ p, t.ι p → K, ∀ x, t.val x = ∑ s, ∏ p, u s p (x p) := by
  have key : ∀ (L : ∀ p, t.ι p → Fin r → K) (x : ∀ p, t.ι p),
      (∑ y : I → Fin r, (∏ p, L p (x p) (y p)) * (if ∀ i j, y i = y j then 1 else 0)) =
        ∑ s, ∏ p, L p (x p) s := by
    intro L x
    let p₀ : I := Classical.arbitrary I
    symm
    refine Finset.sum_of_injOn (fun s _ => s) (fun a _ b _ h => congr_fun h p₀) (fun _ _ => by simp)
      (fun y _ hy => ?_) (fun s _ => by simp)
    rw [if_neg, mul_zero]
    intro h
    exact hy ⟨y p₀, by simp, funext fun p => h p₀ p⟩
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨fun s p a => L p a s, fun x => (hL x).trans (key L x)⟩
  · rintro ⟨u, hu⟩
    exact ⟨fun p a s => u s p a, fun x => (hu x).trans (key (fun p a s => u s p a) x).symm⟩

/-- A tensor of rank at most r is a sum of r restrictions of 1. -/
theorem RankLE.sumRestr [Nonempty I] {t : Ten K I} {r : ℕ} (h : RankLE t r) :
    SumRestr t (fun _ : Fin r => (1 : Ten K I)) := by
  obtain ⟨u, hu⟩ := rankLE_iff.1 h
  refine sumRestr_iff.2 ⟨fun s x => ∏ p, u s p (x p), hu, fun s => ?_⟩
  exact Restr.of_map (fun p a => u s p a) (fun _ _ => ()) fun x => (mul_one _).symm

/-- Every tensor has a rank bound: the number of its entries. -/
theorem rankLE_card [Nonempty I] (t : Ten K I) : RankLE t (Fintype.card (∀ p, t.ι p)) := by
  classical
  let p₀ : I := Classical.arbitrary I
  let e := (Fintype.equivFin (∀ p, t.ι p)).symm
  refine rankLE_iff.2 ⟨fun s p a => if a = e s p then (if p = p₀ then t.val (e s) else 1) else 0,
    fun x => ?_⟩
  rw [Finset.sum_eq_single (e.symm x)]
  · simp
  · intro s _ hs
    have : x ≠ e s := fun h => hs (by rw [h]; simp)
    obtain ⟨p, hp⟩ := Function.ne_iff.1 this
    exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)
  · simp

end Ten

namespace Spec

open Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (F : Spec K I)

/-- F is monotone for restriction. -/
theorem mono {s t : Ten K I} (h : Restr s t) : F.F s ≤ F.F t := by
  simpa using F.le_sum s _ h.sumRestr

/-- Equivalent tensors have the same price. -/
theorem congr {s t : Ten K I} (h : Equi s t) : F.F s = F.F t :=
  le_antisymm (F.mono h.1) (F.mono h.2)

/-- F of the product of a family indexed by 0, …, n-1. -/
theorem prod_fin {n : ℕ} (b : Fin n → Ten K I) : F.F (Ten.prod b) = ∏ k, F.F (b k) := by
  induction n with
  | zero => rw [F.congr (Equi.prod_empty b), F.one]; simp
  | succ n ih => rw [F.congr (Equi.prod_fin_succ b), F.mul, ih, Fin.prod_univ_succ]

/-- F of the product of a family. -/
theorem prod {κ : Type} [Fintype κ] [DecidableEq κ] (b : κ → Ten K I) :
    F.F (Ten.prod b) = ∏ k, F.F (b k) := by
  rw [F.congr (Equi.prod_reindex b (Fintype.equivFin κ).symm), F.prod_fin]
  exact Fintype.prod_equiv (Fintype.equivFin κ).symm _ _ fun _ => rfl

/-- F of a power. -/
theorem kpow (t : Ten K I) (k : ℕ) : F.F (Ten.kpow t k) = F.F t ^ k := by
  rw [kpow_eq_prod, F.prod]; simp

/-- F is 0 at a tensor whose array is 0. -/
theorem zero {t : Ten K I} (h : ∀ x, t.val x = 0) : F.F t = 0 := by
  refine le_antisymm ?_ (F.nonneg t)
  simpa using F.le_sum t (fun k : Empty => k.elim) (SumRestr.of_zero h _)

/-- F is at least 1 at a tensor with an entry that is not 0. -/
theorem one_le [Nonempty I] {t : Ten K I} {y : ∀ p, t.ι p} (h : t.val y ≠ 0) : 1 ≤ F.F t := by
  rw [← F.one]
  exact F.mono (Restr.one_le h)

/-- F is at most the rank. -/
theorem le_rank [Nonempty I] {t : Ten K I} {r : ℕ} (h : RankLE t r) : F.F t ≤ r := by
  simpa [F.one] using F.le_sum t _ h.sumRestr

/-- F is at most the number of entries. -/
theorem le_card [Nonempty I] (t : Ten K I) : F.F t ≤ Fintype.card (∀ p, t.ι p) :=
  F.le_rank (rankLE_card t)

/-- F is subadditive for sums of arrays. -/
theorem le_sum_val {κ : Type} [Fintype κ] (s : Ten K I) (v : κ → (∀ p, s.ι p) → K)
    (h : ∀ x, s.val x = ∑ k, v k x) : F.F s ≤ ∑ k, F.F (s.withVal (v k)) :=
  F.le_sum s _ (SumRestr.of_withVal s v h)

/-- A restriction of a product costs at most the product of the prices. -/
theorem le_mul {s t u : Ten K I} (h : Restr s (t * u)) : F.F s ≤ F.F t * F.F u := by
  rw [← F.mul]; exact F.mono h

/-- A restriction of the product of a family costs at most the product of the prices. -/
theorem le_prod {κ : Type} [Fintype κ] [DecidableEq κ] {s : Ten K I} {b : κ → Ten K I}
    (h : Restr s (Ten.prod b)) : F.F s ≤ ∏ k, F.F (b k) := by
  rw [← F.prod]; exact F.mono h

/-- The pull-back of a spectral point along a map π of parties: a tensor over J costs what it costs
if the leg j is held by π j. -/
def pull (F : Spec K I) (π : J → I) : Spec K J where
  F t := F.F (Ten.push π t)
  nonneg _ := F.nonneg _
  one := by rw [F.congr (Equi.push_one π), F.one]
  mul s t := by rw [F.congr (Equi.push_mul π s t), F.mul]
  le_sum s b h := F.le_sum _ _ (h.push π)

@[simp] theorem pull_F (π : J → I) (t : Ten K J) : (F.pull π).F t = F.F (Ten.push π t) := rfl

end Spec

end Ov
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Networks

A tensor that is the value of a network is a restriction of the product of the wires on the edges of the
network, wherever its vertices are placed. The paper uses special cases: in Lemma lem:exponents, that ⟨q⟩_uw
is a restriction of ⟨q⟩_uv ⟨q⟩_vw, and the same for trees; and Lemma lem:hubs. The statements are about
functions, not graphs: a vertex v has a table T v, a function of all labels, which is *local*: it depends
only on the labels of the edges at v and on the indices held by the party of v.
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Contraction with one tensor. The legs of t are at vertices (the leg l at ρ l), every vertex v is
placed at the party ξ v and has a local table T v: it depends only on the legs of s that are held by
the party ξ v and on the legs of t at v. If s is the sum over all labels of the legs of t of the
product of the tables and of t, then s is a restriction of t, with the legs at their places. -/
theorem Restr.of_contract {L : Type} [Fintype L] [DecidableEq L] (π : J → I) (ξ : V → I)
    (ρ : L → V) (s : Ten K J) (t : Ten K L) (T : V → (∀ j, s.ι j) → (∀ l, t.ι l) → K)
    (hT : ∀ v x x' y y', (∀ j, π j = ξ v → x j = x' j) → (∀ l, ρ l = v → y l = y' l) →
      T v x y = T v x' y')
    (h : ∀ x, s.val x = ∑ y, (∏ v, T v x y) * t.val y) :
    Restr (Ten.push π s) (Ten.push (fun l => ξ (ρ l)) t) := by
  classical
  rcases isEmpty_or_nonempty (∀ j, s.ι j) with hs | ⟨⟨x₀⟩⟩
  · exact ⟨fun _ _ _ => 0, fun x => (hs.false fun j => x (π j) ⟨j, rfl⟩).elim⟩
  rcases isEmpty_or_nonempty (∀ l, t.ι l) with ht | ⟨⟨y₀⟩⟩
  · refine ⟨fun _ _ _ => 0, fun x => ?_⟩
    rw [push_val, h, Finset.univ_eq_empty, Finset.sum_empty]
    have : IsEmpty (∀ q, (Ten.push (fun l => ξ (ρ l)) t).ι q) :=
      ⟨fun y => ht.false fun l => y (ξ (ρ l)) ⟨l, rfl⟩⟩
    rw [app, Finset.univ_eq_empty, Finset.sum_empty]
  let ex : ∀ q, (∀ j : {j : J // π j = q}, s.ι j.1) → ∀ j, s.ι j :=
    fun q a j => if hj : π j = q then a ⟨j, hj⟩ else x₀ j
  let ey : ∀ q, (∀ l : {l : L // ξ (ρ l) = q}, t.ι l.1) → ∀ l, t.ι l :=
    fun q b l => if hl : ξ (ρ l) = q then b ⟨l, hl⟩ else y₀ l
  refine ⟨fun q a b => ∏ v : {v : V // ξ v = q}, T v.1 (ex q a) (ey q b), fun x => ?_⟩
  rw [push_val, h, app_eq_appG, appG]
  symm
  refine Fintype.sum_equiv (pushEquiv (fun l => ξ (ρ l)) t.ι) _ _ fun y => ?_
  congr 1
  rw [← Fintype.prod_fiberwise ξ]
  refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun v _ => ?_
  obtain ⟨v, rfl⟩ := v
  refine hT v _ _ _ _ (fun j hj => ?_) (fun l hl => ?_)
  · have : ex (ξ v) (x (ξ v)) j = x (ξ v) ⟨j, hj⟩ := dif_pos hj
    rw [this]
    clear this
    revert hj
    generalize ξ v = q
    rintro rfl
    rfl
  · subst hl
    exact dif_pos rfl

section Outer

variable {κ : Type} [Fintype κ] [DecidableEq κ] {M : κ → Type} [∀ k, Fintype (M k)]
  [∀ k, DecidableEq (M k)]

/-- The product of tensors with separate legs. -/
def outer (t : ∀ k, Ten K (M k)) : Ten K (Σ k, M k) where
  ι l := (t l.1).ι l.2
  val y := ∏ k, (t k).val fun m => y ⟨k, m⟩

theorem outer_val (t : ∀ k, Ten K (M k)) (y : ∀ l, (outer t).ι l) :
    (outer t).val y = ∏ k, (t k).val fun m => y ⟨k, m⟩ := rfl

/-- Giving the legs of a product with separate legs to parties. -/
theorem Equi.push_outer (π : (Σ k, M k) → I) (t : ∀ k, Ten K (M k)) :
    Equi (Ten.push π (outer t)) (Ten.prod fun k => Ten.push (fun m => π ⟨k, m⟩) (t k)) :=
  Equi.of_equiv
    (fun _ => ⟨fun y k j => y ⟨⟨k, j.1⟩, j.2⟩, fun z l => z l.1.1 ⟨l.1.2, l.2⟩,
      fun _ => rfl, fun _ => rfl⟩)
    fun _ => rfl

end Outer

section Two

variable {L L' : Type} [Fintype L] [DecidableEq L] [Fintype L'] [DecidableEq L']

/-- The product of two tensors with separate legs. -/
def outer₂ (s : Ten K L) (t : Ten K L') : Ten K (L ⊕ L') where
  ι l := Sum.elim s.ι t.ι l
  fin l := match l with
    | Sum.inl l => s.fin l
    | Sum.inr l => t.fin l
  dec l := match l with
    | Sum.inl l => s.dec l
    | Sum.inr l => t.dec l
  val y := s.val (fun l => y (Sum.inl l)) * t.val (fun l => y (Sum.inr l))

/-- Giving the legs of a product of two tensors with separate legs to parties. -/
theorem Equi.push_outer₂ (π : L ⊕ L' → I) (s : Ten K L) (t : Ten K L') :
    Equi (Ten.push π (outer₂ s t))
      (Ten.push (fun l => π (Sum.inl l)) s * Ten.push (fun l => π (Sum.inr l)) t) :=
  Equi.of_equiv
    (fun q => ⟨fun y => (fun l => y ⟨Sum.inl l.1, l.2⟩, fun l => y ⟨Sum.inr l.1, l.2⟩),
      fun z l => match l with
        | ⟨Sum.inl l, h⟩ => z.1 ⟨l, h⟩
        | ⟨Sum.inr l, h⟩ => z.2 ⟨l, h⟩,
      fun y => by funext l; obtain ⟨l | l, h⟩ := l <;> rfl, fun z => rfl⟩)
    fun _ => rfl

end Two

/-- A sum over pairs of labels that must be equal. -/
theorem sum_unit_two {E : Type} [Fintype E] [DecidableEq E] (n : E → ℕ)
    (g : (∀ e, Fin 2 → Fin (n e)) → K) :
    ∑ z : ∀ e, Fin 2 → Fin (n e), g z * ∏ e, (unit K (Fin 2) (n e)).val (z e) =
      ∑ l : ∀ e, Fin (n e), g fun e _ => l e := by
  symm
  refine Finset.sum_of_injOn (fun l e _ => l e) (fun l _ l' _ h => ?_) (fun _ _ => by simp)
    (fun z _ hz => ?_) (fun l _ => ?_)
  · funext e
    exact congr_fun (congr_fun h e) 0
  · have : ∃ e, ¬ ∀ i j, z e i = z e j := by
      by_contra hcon
      push Not at hcon
      exact hz ⟨fun e => z e 0, by simp, funext fun e => funext fun i => hcon e 0 i⟩
    obtain ⟨e, he⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ e), mul_zero]
    exact if_neg he
  · rw [Finset.prod_eq_one, mul_one]
    intro e _
    exact if_pos fun _ _ => rfl

/-- **Networks.** The vertices v are placed at the parties ξ v, the legs j of s are held
by the parties π j. There are edges e with labels in Λ e and ends a e, b e, and tensors t k with
their legs m at the vertices ρ k m. Each vertex has a local table T v: it depends only on the legs of
s held by the party ξ v, on the labels of the edges at v, and on the legs of the t k at v. If s is
the sum over all labels of the product of the tables and of the t k, then s is a restriction of the
product of the edges and of the t k, all at their places. -/
theorem Restr.of_network {E κ : Type} [Fintype E] [DecidableEq E] [Fintype κ] [DecidableEq κ]
    {M : κ → Type} [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)]
    (π : J → I) (ξ : V → I) (s : Ten K J) (Λ : E → Type) [∀ e, Fintype (Λ e)] (a b : E → V)
    (t : ∀ k, Ten K (M k)) (ρ : ∀ k, M k → V)
    (T : V → (∀ j, s.ι j) → (∀ e, Λ e) → (∀ k m, (t k).ι m) → K)
    (hT : ∀ v x x' l l' y y', (∀ j, π j = ξ v → x j = x' j) →
      (∀ e, a e = v ∨ b e = v → l e = l' e) → (∀ k m, ρ k m = v → y k m = y' k m) →
      T v x l y = T v x' l' y')
    (h : ∀ x, s.val x = ∑ l : ∀ e, Λ e, ∑ y : ∀ k m, (t k).ι m,
      (∏ v, T v x l y) * ∏ k, (t k).val (y k)) :
    Restr (Ten.push π s)
      (Ten.prod (fun e => wire K (Fintype.card (Λ e)) (ξ (a e)) (ξ (b e))) *
        Ten.prod (fun k => Ten.push (fun m => ξ (ρ k m)) (t k))) := by
  classical
  let n : E → ℕ := fun e => Fintype.card (Λ e)
  let eq : ∀ e, Fin (n e) ≃ Λ e := fun e => (Fintype.equivFin (Λ e)).symm
  let U : Ten K (Σ _ : E, Fin 2) := outer fun e => unit K (Fin 2) (n e)
  let ρ' : (Σ _ : E, Fin 2) ⊕ (Σ k, M k) → V :=
    Sum.elim (fun l => ![a l.1, b l.1] l.2) (fun l => ρ l.1 l.2)
  let T' : V → (∀ j, s.ι j) → (∀ l, (outer₂ U (outer t)).ι l) → K := fun v x y =>
    T v x (fun e => eq e (if a e = v then y (Sum.inl ⟨e, 0⟩) else y (Sum.inl ⟨e, 1⟩)))
      (fun k m => y (Sum.inr ⟨k, m⟩))
  have key : Restr (Ten.push π s) (Ten.push (fun l => ξ (ρ' l)) (outer₂ U (outer t))) := by
    refine Restr.of_contract π ξ ρ' s (outer₂ U (outer t)) T' (fun v x x' y y' hx hy => ?_)
      fun x => ?_
    · refine hT v _ _ _ _ _ _ hx (fun e he => ?_) fun k m hm => hy (Sum.inr ⟨k, m⟩) hm
      by_cases ha : a e = v
      · simp only [ha]
        exact congr_arg (eq e) (hy (Sum.inl ⟨e, 0⟩) ha)
      · simp only [ha]
        exact congr_arg (eq e) (hy (Sum.inl ⟨e, 1⟩) (he.resolve_left ha))
    · rw [h]
      let Φ : (∀ l, (outer₂ U (outer t)).ι l) ≃
          (∀ e, Fin 2 → Fin (n e)) × (∀ k m, (t k).ι m) :=
        ⟨fun y => (fun e i => y (Sum.inl ⟨e, i⟩), fun k m => y (Sum.inr ⟨k, m⟩)),
          fun z l => match l with
            | Sum.inl l => z.1 l.1 l.2
            | Sum.inr l => z.2 l.1 l.2,
          fun y => by funext l; rcases l with l | l <;> rfl, fun z => rfl⟩
      let g : (∀ e, Fin 2 → Fin (n e)) → (∀ k m, (t k).ι m) → K := fun z y =>
        (∏ v, T v x (fun e => eq e (if a e = v then z e 0 else z e 1)) y) *
          ∏ k, (t k).val (y k)
      have e1 : ∑ y, (∏ v, T' v x y) * (outer₂ U (outer t)).val y =
          ∑ z : (∀ e, Fin 2 → Fin (n e)) × (∀ k m, (t k).ι m),
            g z.1 z.2 * ∏ e, (unit K (Fin 2) (n e)).val (z.1 e) := by
        refine Fintype.sum_equiv Φ _ _ fun y => ?_
        show (∏ v, T' v x y) * ((∏ e, (unit K (Fin 2) (n e)).val ((Φ y).1 e)) *
          ∏ k, (t k).val ((Φ y).2 k)) = (∏ v, T' v x y) * (∏ k, (t k).val ((Φ y).2 k)) *
            ∏ e, (unit K (Fin 2) (n e)).val ((Φ y).1 e)
        ring
      have e2 : ∀ y : ∀ k m, (t k).ι m,
          ∑ z : ∀ e, Fin 2 → Fin (n e), g z y * ∏ e, (unit K (Fin 2) (n e)).val (z e) =
            ∑ l : ∀ e, Λ e, (∏ v, T v x l y) * ∏ k, (t k).val (y k) := by
        intro y
        rw [sum_unit_two n fun z => g z y]
        refine Fintype.sum_equiv (Equiv.piCongrRight eq) _ _ fun l => ?_
        simp only [g, ite_self]
        rfl
      rw [e1, Fintype.sum_prod_type_right, Finset.sum_comm]
      exact Finset.sum_congr rfl fun y _ => (e2 y).symm
  refine key.trans ((Equi.push_outer₂ _ U (outer t)).1.trans (Restr.mul ?_ ?_))
  · refine (Equi.push_outer (fun l : Σ _ : E, Fin 2 => ξ (ρ' (Sum.inl l))) _).1.trans
      (Restr.prod fun e => ?_)
    have : (fun m => ξ (ρ' (Sum.inl ⟨e, m⟩))) = ![ξ (a e), ξ (b e)] := by
      funext m
      fin_cases m <;> rfl
    rw [this]
    exact Restr.refl _
  · exact (Equi.push_outer (fun l : Σ k, M k => ξ (ρ' (Sum.inr l))) t).1

/-- Networks without other tensors: if s is the sum over all labels of the edges of the product of
local tables, then s is a restriction of the product of the wires on the edges, at their places. -/
theorem Restr.of_edges {E : Type} [Fintype E] [DecidableEq E]
    (π : J → I) (ξ : V → I) (s : Ten K J) (Λ : E → Type) [∀ e, Fintype (Λ e)] (a b : E → V)
    (T : V → (∀ j, s.ι j) → (∀ e, Λ e) → K)
    (hT : ∀ v x x' l l', (∀ j, π j = ξ v → x j = x' j) →
      (∀ e, a e = v ∨ b e = v → l e = l' e) → T v x l = T v x' l')
    (h : ∀ x, s.val x = ∑ l : ∀ e, Λ e, ∏ v, T v x l) :
    Restr (Ten.push π s) (Ten.prod fun e => wire K (Fintype.card (Λ e)) (ξ (a e)) (ξ (b e))) := by
  have := Restr.of_network (κ := Empty) (M := fun _ => Empty) π ξ s Λ a b
    (fun k => k.elim) (fun k => k.elim) (fun v x l _ => T v x l)
    (fun v x x' l l' _ _ hx hl _ => hT v x x' l l' hx hl)
    (fun x => by rw [h]; refine Finset.sum_congr rfl fun l _ => ?_
                 rw [Fintype.sum_unique]; simp)
  exact this.trans (((Equi.refl _).mul (Equi.prod_empty _)).trans (Equi.mul_one _)).1

end Ten

end Ov
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Unit tensors and wires

Relations between unit tensors, whose legs may be at any parties, also several at one party, and between wires. They are
what the proof of Lemma lem:exponents (`Paper/Tensors.lean`) uses.
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

/-- A function f ≥ 1 on the positive integers that is multiplicative and monotone is a power function:
f(n) = n^e with e = log₂ f(2). -/
theorem eq_rpow_of_mul_mono (f : ℕ → ℝ) (h1 : ∀ n, 1 ≤ n → 1 ≤ f n)
    (hmul : ∀ m n, 1 ≤ m → 1 ≤ n → f (m * n) = f m * f n)
    (hmono : ∀ m n, 1 ≤ m → m ≤ n → f m ≤ f n) (n : ℕ) (hn : 1 ≤ n) :
    f n = (n : ℝ) ^ Real.logb 2 (f 2) := by
  have hone : f 1 = 1 := by
    have := hmul 1 1 le_rfl le_rfl
    have h0 := h1 1 le_rfl
    nlinarith
  have hpow : ∀ m, 1 ≤ m → ∀ k, f (m ^ k) = f m ^ k := by
    intro m hm k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hmul _ _ (Nat.one_le_pow _ _ hm) hm, ih, pow_succ]
  have hfpos : ∀ m, 1 ≤ m → 0 < f m := fun m hm => lt_of_lt_of_le one_pos (h1 m hm)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set a := Real.log (f 2) with ha
  have ha0 : 0 ≤ a := Real.log_nonneg (h1 2 (by norm_num))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set x := Real.log (f n) * Real.log 2 - a * Real.log n with hx
  have key : ∀ k : ℕ, |(k : ℝ) * x| ≤ a * Real.log 2 := by
    intro k
    set m := Nat.log 2 (n ^ k)
    have hnk : n ^ k ≠ 0 := pow_ne_zero _ (by omega)
    have hm1 : 2 ^ m ≤ n ^ k := Nat.pow_log_le_self 2 hnk
    have hm2 : n ^ k ≤ 2 ^ (m + 1) := (Nat.lt_pow_succ_log_self (by norm_num) _).le
    have f1 : f 2 ^ m ≤ f n ^ k := by
      rw [← hpow 2 (by norm_num), ← hpow n hn]
      exact hmono _ _ (Nat.one_le_two_pow) hm1
    have f2 : f n ^ k ≤ f 2 ^ (m + 1) := by
      rw [← hpow 2 (by norm_num), ← hpow n hn]
      exact hmono _ _ (Nat.one_le_pow _ _ hn) hm2
    have g1 : (m : ℝ) * a ≤ k * Real.log (f n) := by
      have := Real.log_le_log (pow_pos (hfpos 2 (by norm_num)) m) f1
      rwa [Real.log_pow, Real.log_pow] at this
    have g2 : (k : ℝ) * Real.log (f n) ≤ (m + 1) * a := by
      have := Real.log_le_log (pow_pos (hfpos n hn) k) f2
      rw [Real.log_pow, Real.log_pow] at this
      exact_mod_cast this
    have g3 : (m : ℝ) * Real.log 2 ≤ k * Real.log n := by
      have : ((2 : ℝ) ^ m) ≤ (n : ℝ) ^ k := by exact_mod_cast hm1
      have := Real.log_le_log (by positivity) this
      rwa [Real.log_pow, Real.log_pow] at this
    have g4 : (k : ℝ) * Real.log n ≤ (m + 1) * Real.log 2 := by
      have : ((n : ℝ) ^ k) ≤ (2 : ℝ) ^ (m + 1) := by exact_mod_cast hm2
      have := Real.log_le_log (by positivity) this
      rw [Real.log_pow, Real.log_pow] at this
      exact_mod_cast this
    rw [abs_le]
    constructor
    · have e1 := mul_le_mul_of_nonneg_right g1 hl2.le
      have e2 := mul_le_mul_of_nonneg_left g4 ha0
      rw [hx]
      nlinarith
    · have e1 := mul_le_mul_of_nonneg_right g2 hl2.le
      have e2 := mul_le_mul_of_nonneg_left g3 ha0
      rw [hx]
      nlinarith
  have hx0 : x = 0 := by
    by_contra hne
    have hxp : 0 < |x| := abs_pos.2 hne
    obtain ⟨k, hk⟩ := exists_nat_gt (a * Real.log 2 / |x|)
    have := key k
    rw [abs_mul, Nat.abs_cast] at this
    rw [div_lt_iff₀ hxp] at hk
    linarith
  have hfin : Real.log (f n) = Real.logb 2 (f 2) * Real.log n := by
    rw [Real.logb, div_mul_eq_mul_div, eq_div_iff hl2.ne']
    linarith
  rw [Real.rpow_def_of_pos hnpos, mul_comm, ← hfin, Real.exp_log (hfpos n hn)]

namespace Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-! ### Unit tensors -/

/-- The entry of a unit tensor at equal indices is 1. -/
theorem unit_val_of {r : ℕ} {x : J → Fin r} (h : ∀ i j, x i = x j) : (unit K J r).val x = 1 :=
  if_pos h

/-- The other entries of a unit tensor are 0. -/
theorem unit_val_not {r : ℕ} {x : J → Fin r} (h : ¬ ∀ i j, x i = x j) :
    (unit K J r).val x = 0 :=
  if_neg h

theorem unit_val_congr {L : Type} [Fintype L] [DecidableEq L] {r r' : ℕ} {x : J → Fin r}
    {y : L → Fin r'} (h : (∀ i j, x i = x j) ↔ ∀ i j, y i = y j) :
    (unit K J r).val x = (unit K L r').val y := by
  by_cases hx : ∀ i j, x i = x j
  · rw [unit_val_of hx, unit_val_of (h.1 hx)]
  · rw [unit_val_not hx, unit_val_not fun hy => hx (h.2 hy)]

/-- A smaller unit tensor is a restriction of a larger one. -/
theorem Restr.unit_mono {m n : ℕ} (h : m ≤ n) : Restr (unit K J m) (unit K J n) :=
  Restr.of_map' (fun _ => Fin.castLE h) fun x =>
    unit_val_congr (x := x) (y := fun p => Fin.castLE h (x p))
      ⟨fun hx i j => congr_arg _ (hx i j), fun hx i j => Fin.castLE_injective h (hx i j)⟩

/-- The product of the unit tensors of sizes m and n is the one of size m·n. -/
theorem Equi.unit_mul (m n : ℕ) : Equi (unit K J (m * n)) (unit K J m * unit K J n) :=
  Equi.symm <| Equi.of_equiv (fun _ => finProdFinEquiv) fun x => by
    change J → Fin m × Fin n at x
    show (unit K J m).val (fun p => (x p).1) * (unit K J n).val (fun p => (x p).2) =
      (unit K J (m * n)).val fun p => finProdFinEquiv (x p)
    by_cases h1 : ∀ i j, (x i).1 = (x j).1
    · by_cases h2 : ∀ i j, (x i).2 = (x j).2
      · rw [unit_val_of h1, unit_val_of h2, unit_val_of, _root_.mul_one]
        exact fun i j => congr_arg _ (Prod.ext (h1 i j) (h2 i j))
      · have hn : ¬ ∀ i j, finProdFinEquiv (x i) = finProdFinEquiv (x j) := fun h =>
          h2 fun i j => (Prod.ext_iff.1 (finProdFinEquiv.injective (h i j))).2
        rw [unit_val_not hn, unit_val_not h2, mul_zero]
    · have hn : ¬ ∀ i j, finProdFinEquiv (x i) = finProdFinEquiv (x j) := fun h =>
        h1 fun i j => (Prod.ext_iff.1 (finProdFinEquiv.injective (h i j))).1
      rw [unit_val_not hn, unit_val_not h1, zero_mul]

/-- The unit tensor of size 1 is 1. -/
theorem Equi.unit_one : Equi (unit K J 1) 1 :=
  Equi.of_equiv (fun _ => show Fin 1 ≃ Unit from Equiv.ofUnique _ _) fun x => by
    exact unit_val_of fun i j => Subsingleton.elim (α := Fin 1) _ _

/-- Several legs of a unit tensor at one party are as good as one leg. -/
theorem Equi.push_unit {L : Type} [Fintype L] [DecidableEq L] (ρ : L → J) (hρ : ρ.Surjective)
    (n : ℕ) : Equi (Ten.push ρ (unit K L n)) (unit K J n) := by
  classical
  constructor
  · let w : ∀ q, ({l : L // ρ l = q} → Fin n) → K := fun q a =>
      if ∀ l l', a l = a l' then 1 else 0
    refine Restr.of_map w (fun q a => a ⟨(hρ q).choose, (hρ q).choose_spec⟩) fun x => ?_
    change ∀ q, {l : L // ρ l = q} → Fin n at x
    show (unit K L n).val (fun l => x (ρ l) ⟨l, rfl⟩) =
      (∏ q, w q (x q)) *
        (unit K J n).val fun q => x q ⟨(hρ q).choose, (hρ q).choose_spec⟩
    have cast : ∀ l q (h' : ρ l = q), x (ρ l) ⟨l, rfl⟩ = x q ⟨l, h'⟩ := by rintro l _ rfl; rfl
    by_cases h : ∀ l l', x (ρ l) ⟨l, rfl⟩ = x (ρ l') ⟨l', rfl⟩
    · rw [unit_val_of h, unit_val_of, Finset.prod_eq_one, _root_.mul_one]
      · rintro q -
        refine if_pos (show ∀ l l', x q l = x q l' from fun l l' => ?_)
        rw [← cast l.1 q l.2, ← cast l'.1 q l'.2]
        exact h _ _
      · intro q q'
        rw [← cast _ _ (hρ q).choose_spec, ← cast _ _ (hρ q').choose_spec]
        exact h _ _
    · rw [unit_val_not h]
      by_cases h1 : ∀ q l l', x q l = x q l'
      · rw [unit_val_not, mul_zero]
        intro h2
        refine h fun i j => ?_
        rw [h1 (ρ i) ⟨i, rfl⟩ ⟨_, (hρ (ρ i)).choose_spec⟩,
          h1 (ρ j) ⟨j, rfl⟩ ⟨_, (hρ (ρ j)).choose_spec⟩]
        exact h2 _ _
      · push Not at h1
        obtain ⟨q, l, l', hq⟩ := h1
        rw [Finset.prod_eq_zero (Finset.mem_univ q), zero_mul]
        exact if_neg (show ¬ ∀ l l', x q l = x q l' from fun h => hq (h l l'))
  · refine Restr.of_map' (fun q a _ => a) fun x => ?_
    refine unit_val_congr (x := x) (y := fun l => x (ρ l)) ⟨fun h i j => h _ _, fun h i j => ?_⟩
    obtain ⟨i, rfl⟩ := hρ i
    obtain ⟨j, rfl⟩ := hρ j
    exact h i j

/-- A pushed unit tensor depends only on the set of parties that hold a leg. -/
theorem Equi.push_unit_congr {L : Type} [Fintype L] [DecidableEq L] (π : J → I) (π' : L → I)
    (h : Set.range π = Set.range π') (n : ℕ) :
    Equi (Ten.push π (unit K J n)) (Ten.push π' (unit K L n)) := by
  classical
  have key : ∀ {L : Type} [Fintype L] [DecidableEq L] (π' : L → I) (S : Finset I)
      (_ : Set.range π' = S),
      Equi (Ten.push π' (unit K L n)) (Ten.push (fun q : S => (q : I)) (unit K S n)) := by
    intro L _ _ π' S hS
    let ρ : L → S := fun l => ⟨π' l, by
      have : π' l ∈ (S : Set I) := hS ▸ Set.mem_range_self l
      exact this⟩
    have hρ : ρ.Surjective := by
      rintro ⟨q, hq⟩
      have : q ∈ Set.range π' := hS ▸ (show q ∈ (S : Set I) from hq)
      obtain ⟨l, hl⟩ := this
      exact ⟨l, Subtype.ext hl⟩
    exact ((Equi.push_push (fun q : S => (q : I)) ρ (unit K L n)).symm.trans
      ((Equi.push_unit ρ hρ n).push _))
  exact (key π (Set.toFinset (Set.range π)) (by simp)).trans
    (key π' (Set.toFinset (Set.range π)) (by simp [h])).symm

/-- A tensor with all its legs at one party is a restriction of 1. -/
theorem Restr.push_const (q : I) (t : Ten K J) : Restr (Ten.push (fun _ => q) t) 1 := by
  classical
  refine Restr.of_map (fun p a => if h : q = p then t.val fun j => a ⟨j, h⟩ else 1)
    (fun _ _ => ()) fun x => ?_
  have key : ∀ f : ∀ p, ∀ j : {j : J // q = p}, t.ι j.1, t.val (fun j => f q ⟨j, rfl⟩) =
      ∏ p, if h : q = p then t.val fun j => f p ⟨j, h⟩ else 1 := by
    intro f
    rw [Finset.prod_eq_single q]
    · simp
    · intro p _ hp
      rw [dif_neg fun h => hp h.symm]
    · simp
  exact (key x).trans (_root_.mul_one _).symm

/-! ### Wires -/

/-- A wire may be read in both directions. -/
theorem Equi.wire_comm (n : ℕ) (p q : I) : Equi (wire K n p q) (wire K n q p) :=
  Equi.push_unit_congr _ _ (by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_cons]
    simp [Set.pair_comm]) n

/-- A wire with both ends at one party is a restriction of 1. -/
theorem Restr.wire_self (n : ℕ) (p : I) : Restr (wire K n p p) 1 := by
  have : (![p, p] : Fin 2 → I) = fun _ => p := by
    funext i; fin_cases i <;> rfl
  rw [wire, this]
  exact Restr.push_const p _

/-- Two parallel wires are one wire, whose dimension is the product. -/
theorem Equi.wire_mul (m n : ℕ) (p q : I) :
    Equi (wire K (m * n) p q) (wire K m p q * wire K n p q) :=
  ((Equi.unit_mul m n).push _).trans (Equi.push_mul _ _ _)

/-- A wire of dimension 1 is 1. -/
theorem Equi.wire_one (p q : I) : Equi (wire K 1 p q) 1 :=
  (Equi.unit_one.push _).trans (Equi.push_one _)

private def tr {n : ℕ} (v : Fin 3) (x l : Fin 2 → Fin n) : K :=
  if v = 0 then (if x 0 = l 0 then 1 else 0) else
    if v = 1 then (if l 0 = l 1 then 1 else 0) else (if x 1 = l 1 then 1 else 0)

private theorem tr_sum {n : ℕ} (x : Fin 2 → Fin n) :
    (unit K (Fin 2) n).val x = ∑ l : Fin 2 → Fin n, ∏ v, tr (K := K) v x l := by
  rw [Finset.sum_eq_single (fun _ => x 0)]
  · rcases eq_or_ne (x 0) (x 1) with h | h
    · rw [unit_val_of (by simp [Fin.forall_fin_two, h])]
      simp [tr, h]
    · rw [unit_val_not (by simp [Fin.forall_fin_two, h])]
      simp [Fin.prod_univ_succ, tr, h.symm]
  · intro l _ hl
    by_cases h0 : x 0 = l 0
    · by_cases h1 : l 0 = l 1
      · refine absurd (funext fun i => ?_) hl
        fin_cases i
        · exact h0.symm
        · exact (h0.trans h1).symm
      · simp [Fin.prod_univ_succ, tr, h1]
    · simp [Fin.prod_univ_succ, tr, h0]
  · simp

/-- The wire from p to q is a restriction of the product of the wires from p to r and from r to q. -/
theorem Restr.wire_trans (n : ℕ) (p q r : I) :
    Restr (wire K n p q) (wire K n p r * wire K n r q) := by
  classical
  have h := Restr.of_edges (V := Fin 3) (E := Fin 2) (J := Fin 2) (K := K) ![p, q] ![p, r, q]
    (unit K (Fin 2) n) (fun _ => Fin n) ![0, 1] ![1, 2] tr
    (by
      intro v x x' l l' hx hl
      change Fin 2 → Fin n at x x'
      fin_cases v
      · have h0 : x 0 = x' 0 := hx 0 rfl
        have h1 := hl 0 (Or.inl rfl)
        simp [tr, h0, h1]
      · have h0 := hl 0 (Or.inr rfl)
        have h1 := hl 1 (Or.inl rfl)
        simp [tr, h0, h1]
      · have h0 : x 1 = x' 1 := hx 1 rfl
        have h1 := hl 1 (Or.inr rfl)
        simp [tr, h0, h1]) tr_sum
  refine h.trans ((Equi.prod_fin_two _).1.trans ?_)
  simp only [Fintype.card_fin]
  exact Restr.refl _

/-- Moving legs: the leg j can be moved from π' j to π j through a wire of its dimension. -/
theorem Restr.move (π π' : J → I) (t : Ten K J) :
    Restr (Ten.push π t)
      (Ten.prod (fun j => wire K (Fintype.card (t.ι j)) (π j) (π' j)) * Ten.push π' t) := by
  classical
  have h := Restr.of_network (V := J ⊕ J) (E := J) (κ := Unit) (M := fun _ => J) π
    (Sum.elim π π') t t.ι Sum.inl Sum.inr (fun _ => t) (fun _ j => Sum.inr j)
    (fun v x l y => match v with
      | Sum.inl j => if x j = l j then 1 else 0
      | Sum.inr j => if l j = y () j then 1 else 0)
    (by
      intro v x x' l l' y y' hx hl hy
      rcases v with j | j
      · simp only [hx j rfl, hl j (Or.inl rfl)]
      · simp only [hl j (Or.inr rfl), hy () j rfl])
    (by
      intro x
      rw [Finset.sum_eq_single x]
      · rw [Finset.sum_eq_single (fun _ => x)]
        · simp
        · intro y _ hy
          have : ∃ j, ¬ x j = y () j := by
            by_contra hcon
            push Not at hcon
            exact hy (funext fun _ => funext fun j => (hcon j).symm)
          obtain ⟨j, hj⟩ := this
          rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inr j)) (if_neg hj), zero_mul]
        · simp
      · intro l _ hl
        have : ∃ j, ¬ x j = l j := by
          by_contra hcon
          push Not at hcon
          exact hl (funext fun j => (hcon j).symm)
        obtain ⟨j, hj⟩ := this
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl j)) (if_neg hj), zero_mul]
      · simp)
  refine h.trans (Restr.mul (Restr.refl _) ?_)
  exact (Equi.prod_unique _).1

end Ten

namespace Spec

open Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (F : Spec K I)

/-- F of a pushed unit tensor of size at least 1 is at least 1. -/
theorem one_le_unit [Nonempty I] (π : J → I) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ F.F (Ten.push π (unit K J n)) := by
  refine F.one_le (y := fun _ _ => ⟨0, hn⟩) ?_
  show ite _ _ _ ≠ (0 : K)
  simp

/-- F of a unit tensor that has a leg is at most its size. -/
theorem unit_le [Nonempty J] (π : J → I) (n : ℕ) : F.F (Ten.push π (unit K J n)) ≤ n := by
  have h : SumRestr (unit K J n) (fun _ : Fin n => (1 : Ten K J)) :=
    RankLE.sumRestr (Restr.refl (unit K J n))
  have := F.le_sum _ _ (h.push π)
  simpa [F.congr (Equi.push_one π), F.one] using this

end Spec

end Ov
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The permanent as a coefficient

The permanent of a matrix is the coefficient of the product of all variables in the product of the linear
forms given by the rows. This coefficient does not change modulo the squares of the variables.
-/

namespace Nc

open Finset MvPolynomial

variable {R : Type*} [CommRing R]

/-- The exponent of the product of all variables. -/
noncomputable def ones (C : Type*) [Fintype C] : C →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1

@[simp] theorem ones_apply {C : Type*} [Fintype C] (c : C) : ones C c = 1 := rfl

section Bij

variable {C I : Type*} [Fintype C] [Fintype I]

theorem sum_single_eq_ones [DecidableEq C] (f : I → C) :
    (∑ i, Finsupp.single (f i) 1 = ones C) ↔ Function.Bijective f := by
  classical
  have hap : ∀ c, (∑ i, Finsupp.single (f i) 1 : C →₀ ℕ) c = #{i | f i = c} := by
    intro c
    rw [Finsupp.finsetSum_apply, Finset.card_filter]
    exact Finset.sum_congr rfl fun i _ => by rw [Finsupp.single_apply]
  rw [Function.bijective_iff_existsUnique]
  constructor
  · intro h c
    have := hap c
    rw [h, ones_apply] at this
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 this.symm
    refine ⟨i, ?_, fun j hj => ?_⟩
    · have : i ∈ ({i | f i = c} : Finset I) := by rw [hi]; simp
      simpa using this
    · have : j ∈ ({i | f i = c} : Finset I) := by simpa using hj
      rw [hi] at this
      simpa using this
  · intro h
    ext c
    rw [hap, ones_apply, Finset.card_eq_one]
    obtain ⟨i, hi, hu⟩ := h c
    refine ⟨i, ?_⟩
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨hu j, fun e => e ▸ hi⟩

variable {N J κ : Type*} [Fintype N] [Fintype J] [Fintype κ] [DecidableEq N]

open scoped Classical in
/-- Expanding a product of sums of terms and taking the coefficient of the product of all variables. -/
theorem coeff_ones_prod (w : N → κ → R) (g : N → κ → J → C) :
    coeff (ones C) (∏ i, ∑ a, MvPolynomial.C (w i a) * ∏ j, (X (g i a j) : MvPolynomial C R)) =
      ∑ f : N → κ, if Function.Bijective (fun p : N × J => g p.1 (f p.1) p.2) then ∏ i, w i (f i)
        else 0 := by
  classical
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, coeff_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, coeff_C_mul, ← Fintype.prod_prod_type'
    (f := fun i j => (X (g i (f i) j) : MvPolynomial C R))]
  have : (∏ p : N × J, (X (g p.1 (f p.1) p.2) : MvPolynomial C R)) =
      monomial (∑ p : N × J, Finsupp.single (g p.1 (f p.1) p.2) 1) 1 := by
    rw [monomial_sum_one]
    rfl
  rw [this, coeff_monomial]
  simp only [sum_single_eq_ones (fun p : N × J => g p.1 (f p.1) p.2)]
  split_ifs <;> simp

open scoped Classical in
theorem sum_perm_eq [DecidableEq C] (w : C → C → R) :
    ∑ σ : Equiv.Perm C, ∏ i, w i (σ i) =
      ∑ f : C → C, if Function.Bijective f then ∏ i, w i (f i) else 0 := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij' (i := fun f hf => Equiv.ofBijective f (Finset.mem_filter.1 hf).2)
    (j := fun σ _ => (σ : C → C)) ?_ ?_ ?_ ?_ ?_
  · simp
  · intro σ _
    simp only [mem_filter, mem_univ, true_and]
    exact σ.bijective
  · intros; rfl
  · intros; ext; rfl
  · intros; rfl

/-- The permanent is a coefficient. -/
theorem permanent_eq_coeff [DecidableEq C] (M : Matrix C C R) :
    M.permanent = coeff (ones C) (∏ i, ∑ j, MvPolynomial.C (M i j) * (X j : MvPolynomial C R)) := by
  classical
  have h := coeff_ones_prod (N := C) (J := Unit) (κ := C) (C := C) (fun i j => M i j) (fun _ a _ => a)
  have h2 : M.permanent = ∑ σ : Equiv.Perm C, ∏ i, M i (σ i) := by
    rw [← Matrix.permanent_transpose]
    rfl
  simp only [Finset.univ_unique, Finset.prod_singleton] at h
  rw [h, h2]
  refine (sum_perm_eq (fun i j => M i j)).trans (Finset.sum_congr rfl fun f _ => ?_)
  have hiff : Function.Bijective f ↔ Function.Bijective fun p : C × Unit => f p.1 :=
    ⟨fun hb => hb.comp (Equiv.prodPUnit C).bijective, fun hb => hb.comp (Equiv.prodPUnit C).symm.bijective⟩
  by_cases hb : Function.Bijective f
  · rw [if_pos hb, if_pos (hiff.1 hb)]
  · rw [if_neg hb, if_neg (fun h' => hb (hiff.2 h'))]

end Bij

section Squares

variable {C : Type*} [Fintype C]

variable (C R) in
/-- The ideal of the squares of the variables. -/
noncomputable def sqIdeal : Ideal (MvPolynomial C R) := Ideal.span (Set.range fun c => X c * X c)

theorem coeff_ones_of_mem {p : MvPolynomial C R} (h : p ∈ sqIdeal R C) : coeff (ones C) p = 0 := by
  classical
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← mul_assoc, coeff_mul_X', coeff_mul_X']
  simp [Finsupp.mem_support_iff]

theorem coeff_ones_congr {p q : MvPolynomial C R}
    (h : Ideal.Quotient.mk (sqIdeal R C) p = Ideal.Quotient.mk (sqIdeal R C) q) :
    coeff (ones C) p = coeff (ones C) q := by
  have := coeff_ones_of_mem (Ideal.Quotient.eq.1 h)
  rwa [coeff_sub, sub_eq_zero] at this

omit [Fintype C] in
theorem mk_X_sq (c : C) : Ideal.Quotient.mk (sqIdeal R C) (X c) ^ 2 = 0 := by
  rw [sq, ← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨c, rfl⟩)

omit [Fintype C] in
/-- Modulo squares, a product of two linear forms in four variables has only two terms. -/
theorem mk_gadget (h : R) (hh : h * 2 = 1) (p q r s : C) :
    Ideal.Quotient.mk (sqIdeal R C)
      ((MvPolynomial.C h * X p + MvPolynomial.C h * X q + MvPolynomial.C h * X r - MvPolynomial.C h * X s) *
        (X p + X q - X r + X s)) = Ideal.Quotient.mk (sqIdeal R C) (X p * X q + X r * X s) := by
  simp only [map_mul, map_add, map_sub]
  have h1 := mk_X_sq (R := R) p
  have h2 := mk_X_sq (R := R) q
  have h3 := mk_X_sq (R := R) r
  have h4 := mk_X_sq (R := R) s
  have h5 : Ideal.Quotient.mk (sqIdeal R C) (MvPolynomial.C h) * 2 = 1 := by
    rw [← map_ofNat (Ideal.Quotient.mk (sqIdeal R C)) 2, ← map_mul, ← map_ofNat MvPolynomial.C 2,
      ← map_mul, hh, map_one, map_one]
  generalize Ideal.Quotient.mk (sqIdeal R C) (X p) = p at *
  generalize Ideal.Quotient.mk (sqIdeal R C) (X q) = q at *
  generalize Ideal.Quotient.mk (sqIdeal R C) (X r) = r at *
  generalize Ideal.Quotient.mk (sqIdeal R C) (X s) = s at *
  generalize Ideal.Quotient.mk (sqIdeal R C) (MvPolynomial.C h) = e at *
  linear_combination e * h1 + e * h2 - e * h3 - e * h4 + (p * q + r * s) * h5

end Squares

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Sums over two families of bits as permanents

`N` is a finite set of incidences with two permutations `σ`, `ρ`. A bit for every orbit of `σ` and a bit for
every orbit of `ρ` are summed over, and every incidence contributes a weight that depends on its two bits.
The sum is a permanent of size `3 * |N|`.
-/

namespace Nc

open Finset MvPolynomial

variable {R : Type*} [CommRing R]
variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The row that is chosen at `n`: `n` itself or its successor. -/
def pick (σ : Equiv.Perm N) (s : N → Bool) (n : N) : N := if s n then n else σ n

omit [Fintype N] [DecidableEq N] in
theorem pick_injective {σ : Equiv.Perm N} {s : N → Bool} (h : ∀ n, s (σ n) = s n) :
    Function.Injective (pick σ s) := by
  intro n m e
  unfold pick at e
  rcases hn : s n <;> rcases hm : s m <;> simp only [hn, hm, if_true, if_false, Bool.false_eq_true] at e
  · exact σ.injective e
  · have := h n
    rw [e, hn, hm] at this
    cases this
  · have := h m
    rw [← e, hn, hm] at this
    cases this
  · exact e

omit [DecidableEq N] in
theorem inv_of_pick_injective {σ : Equiv.Perm N} {s : N → Bool} (h : Function.Injective (pick σ s)) (n : N) :
    s (σ n) = s n := by
  rcases hn : s n <;> rcases hm : s (σ n)
  · rfl
  · have : pick σ s n = pick σ s (σ n) := by simp [pick, hn, hm]
    have := h this
    rw [← this, hn] at hm
    cases hm
  · obtain ⟨m, hm'⟩ := (Finite.injective_iff_surjective.1 h) (σ n)
    unfold pick at hm'
    rcases hs : s m <;> simp only [hs, if_true, if_false, Bool.false_eq_true] at hm'
    · have := σ.injective hm'
      rw [this, hn] at hs
      cases hs
    · rw [hm', hm] at hs
      cases hs
  · rfl

/-- The columns used by the three rows of an incidence. -/
def slot (σ ρ : Equiv.Perm N) (n : N) (a : Bool × Bool × Bool) : Option Bool → N × Option Bool
  | none => (if a.1 then n else σ n, none)
  | some true => (n, some a.1)
  | some false => (if a.2.1 then n else ρ n, some !a.2.2)

omit [DecidableEq N] in
theorem slot_bijective (σ ρ : Equiv.Perm N) (s r q : N → Bool) :
    Function.Bijective (fun p : N × Option Bool => slot σ ρ p.1 (s p.1, r p.1, q p.1) p.2) ↔
      (∀ n, s (σ n) = s n) ∧ (∀ n, r (ρ n) = r n) ∧ ∀ n, s (pick ρ r n) = q n := by
  constructor
  · rintro ⟨h, -⟩
    have h3 : ∀ n, s (pick ρ r n) = q n := by
      intro n
      by_contra hne
      have : ((n, some false) : N × Option Bool) = (pick ρ r n, some true) := by
        apply h
        simp only [slot, pick] at hne ⊢
        congr 2
        revert hne
        generalize s _ = x
        generalize q n = y
        revert x y
        decide
      simp at this
    refine ⟨fun n => inv_of_pick_injective (fun n m e => ?_) n,
      fun n => inv_of_pick_injective (fun n m e => ?_) n, h3⟩
    · have : ((n, none) : N × Option Bool) = (m, none) := h (by
        simp only [slot]
        exact congrArg (fun x => (x, none)) e)
      exact (Prod.mk.inj this).1
    · have : ((n, some false) : N × Option Bool) = (m, some false) := h (by
        simp only [slot]
        rw [← h3 n, ← h3 m, e]
        exact congrArg (fun x => (x, some !s (pick ρ r m))) e)
      exact (Prod.mk.inj this).1
  · intro ⟨h1, h2, h3⟩
    rw [← Finite.injective_iff_bijective]
    have i1 := pick_injective h1
    have i2 := pick_injective h2
    rintro ⟨n, _ | _ | _⟩ ⟨m, _ | _ | _⟩ e <;> simp only [slot, Prod.mk.injEq, reduceCtorEq, and_false,
      Option.some.injEq] at e
    · rw [i1 e.1]
    · rw [i2 e.1]
    · obtain ⟨e1, e2⟩ := e
      have := h3 n
      unfold pick at this
      rw [e1] at this
      rw [this] at e2
      exact absurd e2 (by cases q n <;> decide)
    · obtain ⟨e1, e2⟩ := e
      have := h3 m
      unfold pick at this
      rw [← e1] at this
      rw [this] at e2
      exact absurd e2 (by cases q m <;> decide)
    · rw [e.1]

/-- The indicator of a column. -/
def ind (c₀ : N × Option Bool) (a : R) (c : N × Option Bool) : R := if c = c₀ then a else 0

/-- The matrix. -/
def gridMatrix (h : R) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) :
    Matrix (N × Option Bool) (N × Option Bool) R
  | (n, none), c => ind (n, none) h c + ind (n, some true) h c + ind (σ n, none) h c - ind (n, some false) h c
  | (n, some true), c =>
    ind (n, none) 1 c + ind (n, some true) 1 c - ind (σ n, none) 1 c + ind (n, some false) 1 c
  | (n, some false), c =>
    ind (n, some false) (W n true true) c + ind (n, some true) (W n false true) c +
      ind (ρ n, some false) (W (ρ n) true false) c + ind (ρ n, some true) (W (ρ n) false false) c

theorem sum_ind (c₀ : N × Option Bool) (a : R) :
    ∑ c, MvPolynomial.C (ind c₀ a c) * (X c : MvPolynomial (N × Option Bool) R) =
      MvPolynomial.C a * X c₀ := by
  simp [ind, apply_ite MvPolynomial.C, ite_mul]

/-- The weight of a choice. -/
def wt (ρ : Equiv.Perm N) (W : N → Bool → Bool → R) (n : N) (a : Bool × Bool × Bool) : R :=
  if a.2.1 then W n a.2.2 true else W (ρ n) a.2.2 false

theorem sum_row_none (h : R) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) (n : N) :
    ∑ c, MvPolynomial.C (gridMatrix h σ ρ W (n, none) c) * (X c : MvPolynomial (N × Option Bool) R) =
      MvPolynomial.C h * X (n, none) + MvPolynomial.C h * X (n, some true) +
        MvPolynomial.C h * X (σ n, none) - MvPolynomial.C h * X (n, some false) := by
  simp only [gridMatrix, map_add, map_sub, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_ind]

theorem sum_row_true (h : R) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) (n : N) :
    ∑ c, MvPolynomial.C (gridMatrix h σ ρ W (n, some true) c) * (X c : MvPolynomial (N × Option Bool) R) =
      X (n, none) + X (n, some true) - X (σ n, none) + X (n, some false) := by
  simp only [gridMatrix, map_add, map_sub, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_ind, map_one, one_mul]

theorem sum_row_false (h : R) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) (n : N) :
    ∑ c, MvPolynomial.C (gridMatrix h σ ρ W (n, some false) c) * (X c : MvPolynomial (N × Option Bool) R) =
      MvPolynomial.C (W n true true) * X (n, some false) + MvPolynomial.C (W n false true) * X (n, some true) +
        MvPolynomial.C (W (ρ n) true false) * X (ρ n, some false) +
        MvPolynomial.C (W (ρ n) false false) * X (ρ n, some true) := by
  simp only [gridMatrix, map_add, add_mul, Finset.sum_add_distrib, sum_ind]

theorem gridMatrix_permanent_aux (h : R) (hh : h * 2 = 1) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) :
    (gridMatrix h σ ρ W).permanent = coeff (ones (N × Option Bool))
      (∏ n, ∑ a, MvPolynomial.C (wt ρ W n a) * ∏ j, (X (slot σ ρ n a j) : MvPolynomial (N × Option Bool) R)) := by
  rw [permanent_eq_coeff]
  apply coeff_ones_congr
  rw [Fintype.prod_prod_type, map_prod, map_prod]
  refine Finset.prod_congr rfl fun n _ => ?_
  simp only [Fintype.prod_option, Fintype.prod_bool]
  rw [sum_row_none, sum_row_true, sum_row_false, ← mul_assoc, map_mul, mk_gadget h hh, ← map_mul]
  congr 1
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, slot, wt, if_true, if_false, Bool.false_eq_true,
    Bool.not_true, Bool.not_false]
  ring

open scoped Classical in
theorem gridMatrix_permanent (h : R) (hh : h * 2 = 1) (σ ρ : Equiv.Perm N) (W : N → Bool → Bool → R) :
    (gridMatrix h σ ρ W).permanent = ∑ s : N → Bool, ∑ r : N → Bool,
      if (∀ n, s (σ n) = s n) ∧ (∀ n, r (ρ n) = r n) then ∏ n, W n (s n) (r n) else 0 := by
  classical
  rw [gridMatrix_permanent_aux h hh, coeff_ones_prod]
  rw [← (Equiv.arrowProdEquivProdArrow N (fun _ => Bool) (fun _ => Bool × Bool)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← (Equiv.arrowProdEquivProdArrow N (fun _ => Bool) (fun _ => Bool)).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single (fun n => s (pick ρ r n))]
  · have key := slot_bijective σ ρ s r (fun n => s (pick ρ r n))
    simp only [implies_true, and_true] at key
    by_cases hc : (∀ n, s (σ n) = s n) ∧ (∀ n, r (ρ n) = r n)
    · rw [if_pos hc]
      refine (if_pos (key.2 hc)).trans ?_
      have e1 : ∀ n, wt ρ W n (s n, r n, s (pick ρ r n)) =
          (if r n then W n (s n) (r n) else 1) *
            (if r (ρ n) then 1 else W (ρ n) (s (ρ n)) (r (ρ n))) := by
        intro n
        rw [hc.2 n]
        rcases hr : r n <;> simp [wt, pick, hr]
      refine (Finset.prod_congr rfl fun n _ => e1 n).trans ?_
      rw [Finset.prod_mul_distrib, Equiv.prod_comp ρ (fun n => if r n then 1 else W n (s n) (r n)),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun n _ => ?_
      split_ifs <;> simp
    · rw [if_neg hc]
      exact if_neg fun hb => hc (key.1 hb)
  · intro q _ hq
    apply if_neg
    intro hb
    apply hq
    have := (slot_bijective σ ρ s r q).1 hb
    funext n
    exact (this.2.2 n).symm
  · intro hc
    exact absurd (mem_univ _) hc

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Sums over two families of bits, indexed by maps

The permutations of the grid are replaced by maps: all incidences with the same value of a map share a bit.
-/

namespace Nc

open Finset MvPolynomial

section Fibres

variable {N V : Type*} [Fintype N] [DecidableEq N]

/-- A permutation whose cycles are the fibres of a map. -/
theorem exists_perm_fibres (v : N → V) : ∃ σ : Equiv.Perm N, (∀ n, v (σ n) = v n) ∧
    ∀ s : N → Bool, (∀ n, s (σ n) = s n) → ∀ n m, v n = v m → s n = s m := by
  classical
  have h : ∀ y, ∃ f : Equiv.Perm {n // v n = y}, f.IsCycleOn ((univ : Finset {n // v n = y}) : Set _) :=
    fun y => (Finset.exists_cycleOn univ).imp fun f hf => hf.1
  choose f hf using h
  let e := Equiv.sigmaFiberEquiv v
  let σ : Equiv.Perm N := (e.symm.trans (Equiv.sigmaCongrRight f)).trans e
  have hσ : ∀ n, σ n = (f (v n) ⟨n, rfl⟩).1 := fun n => rfl
  refine ⟨σ, fun n => ?_, fun s hs n m e => ?_⟩
  · rw [hσ]
    exact (f (v n) ⟨n, rfl⟩).2
  · have h1 : ∀ y, ∀ x : {n // v n = y}, s (f y x).1 = s x.1 := by
      rintro y ⟨x, rfl⟩
      rw [← hσ]
      exact hs x
    obtain ⟨i, -, hi⟩ := (hf (v m)).exists_pow_eq (mem_univ ⟨n, e⟩) (mem_univ ⟨m, rfl⟩)
    have h2 : ∀ i : ℕ, s ((f (v m) ^ i) ⟨n, e⟩).1 = s n := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, h1, ih]
    rw [← h2 i, hi]

variable {R : Type*} [CommRing R]

open scoped Classical in
/-- A sum over the functions that are constant on the fibres. -/
theorem sum_invariant [Fintype V] [DecidableEq V] {v : N → V} (hv : Function.Surjective v) {σ : Equiv.Perm N}
    (h1 : ∀ n, v (σ n) = v n)
    (h2 : ∀ s : N → Bool, (∀ n, s (σ n) = s n) → ∀ n m, v n = v m → s n = s m) (Φ : (N → Bool) → R) :
    ∑ s : N → Bool, (if ∀ n, s (σ n) = s n then Φ s else 0) = ∑ x : V → Bool, Φ fun n => x (v n) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun x _ n => x (v n)) ?_ ?_ ?_ ?_
  · intro x _
    simp [h1]
  · intro x _ y _ e
    exact hv.injective_comp_right e
  · intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs
    refine ⟨fun y => s (Function.surjInv hv y), mem_univ _, ?_⟩
    funext n
    exact h2 s hs _ _ (Function.surjInv_eq hv _)
  · intros
    rfl

/-- A sum over two families of bits is a permanent. -/
theorem exists_grid {K : Type*} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K] (v : N → V) (w : N → K)
    (hv : Function.Surjective v) (hw : Function.Surjective w) :
    ∃ σ ρ : Equiv.Perm N, (∀ n, w (ρ n) = w n) ∧ ∀ (h : R) (_ : h * 2 = 1) (W : N → Bool → Bool → R),
      (gridMatrix h σ ρ W).permanent =
        ∑ x : V → Bool, ∑ r : K → Bool, ∏ n, W n (x (v n)) (r (w n)) := by
  classical
  obtain ⟨σ, s1, s2⟩ := exists_perm_fibres v
  obtain ⟨ρ, r1, r2⟩ := exists_perm_fibres w
  refine ⟨σ, ρ, r1, fun h hh W => ?_⟩
  rw [gridMatrix_permanent h hh]
  refine Eq.trans ?_ (sum_invariant hv s1 s2 fun s => ∑ r : K → Bool, ∏ n, W n (s n) (r (w n)))
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : ∀ n, s (σ n) = s n
  · rw [if_pos hs]
    refine Eq.trans ?_ (sum_invariant hw r1 r2 fun r => ∏ n, W n (s n) (r n))
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [hs]
  · rw [if_neg hs]
    exact Finset.sum_eq_zero fun r _ => if_neg fun hc => hs hc.1

end Fibres

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The permanent under renaming and padding
-/

namespace Nc

open Finset

variable {R : Type*} [CommSemiring R]
variable {C D E : Type*} [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem permanent_submatrix_equiv (e : D ≃ C) (M : Matrix C C R) :
    (M.submatrix e e).permanent = M.permanent := by
  unfold Matrix.permanent
  refine Fintype.sum_equiv e.permCongr _ _ fun σ => ?_
  refine Fintype.prod_equiv e _ _ fun i => ?_
  simp [Matrix.submatrix_apply, Equiv.permCongr_apply]

/-- A diagonal of ones does not change the permanent. -/
theorem permanent_pad (M : Matrix C C R) :
    (Matrix.fromBlocks M 0 0 (1 : Matrix E E R)).permanent = M.permanent := by
  unfold Matrix.permanent
  symm
  refine Finset.sum_of_injOn (fun τ => Equiv.Perm.sumCongr τ 1) ?_ ?_ ?_ ?_
  · intro τ _ τ' _ e
    have := Equiv.Perm.sumCongrHom_injective (α := C) (β := E) (a₁ := (τ, 1)) (a₂ := (τ', 1)) e
    exact (Prod.mk.inj this).1
  · intro τ _
    simp
  · intro σ _ hσ
    by_contra hne
    apply hσ
    have hfix : ∀ k : E, σ (Sum.inr k) = Sum.inr k := by
      intro k
      by_contra hk
      apply hne
      refine Finset.prod_eq_zero (mem_univ (Sum.inr k)) ?_
      rcases hs : σ (Sum.inr k) with c | e
      · rw [Matrix.fromBlocks_apply₁₂]
        rfl
      · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply_ne]
        rintro rfl
        exact hk hs
    have hmaps : Set.MapsTo σ (Set.range (Sum.inl : C → C ⊕ E)) (Set.range Sum.inl) := by
      rintro _ ⟨c, rfl⟩
      rcases hs : σ (Sum.inl c) with c' | e
      · exact ⟨c', rfl⟩
      · have := σ.injective (hs.trans (hfix e).symm)
        cases this
    obtain ⟨⟨τ, κ⟩, rfl⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
    have : κ = 1 := by
      ext k
      have := hfix k
      simpa using this
    subst this
    exact ⟨τ, by simp, rfl⟩
  · intro τ _
    rw [Fintype.prod_sum_type]
    simp

/-- A square matrix sits in every larger one with the same permanent. -/
theorem exists_permanent_fin (M : Matrix C C R) {S : ℕ} (hS : Fintype.card C ≤ S) :
    ∃ M' : Matrix (Fin S) (Fin S) R, M'.permanent = M.permanent ∧
      ∀ i j, (M' i j = 0 ∨ M' i j = 1) ∨ ∃ c d, M' i j = M c d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hS
  let e : Fin (Fintype.card C + k) ≃ C ⊕ Fin k :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Fintype.equivFin C).symm (Equiv.refl _))
  refine ⟨(Matrix.fromBlocks M 0 0 (1 : Matrix (Fin k) (Fin k) R)).submatrix e e, ?_, fun i j => ?_⟩
  · rw [permanent_submatrix_equiv, permanent_pad]
  · rw [Matrix.submatrix_apply]
    rcases e i with c | a <;> rcases e j with d | b
    · exact Or.inr ⟨c, d, rfl⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inl rfl)
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      split_ifs
      · exact Or.inl (Or.inr rfl)
      · exact Or.inl (Or.inl rfl)

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Low degree is fast (Lemma 1)

A polynomial of degree at most `d` that is computed by an arithmetic circuit with `s` gates has, at every
point, a value that is a sum over parse trees. A parse tree with `i` leaves reads `2 * i - 1` entries of
fixed tables of the circuit and `i` coordinates of the point; only `i ≤ d` occurs.
-/

namespace Nc

open Finset

section Circuits

variable {F : Type*} [CommSemiring F] {σ : Type*}

/-- Entry `k` of the list `l` is a variable, a constant, or the sum or product of two earlier entries. -/
def IsStep (l : ℕ → MvPolynomial σ F) (k : ℕ) : Prop :=
  (∃ i : σ, l k = MvPolynomial.X i) ∨ (∃ a : F, l k = MvPolynomial.C a) ∨
    (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)

/-- `p` is computed by an arithmetic circuit with `s` gates (inputs and constants count as gates). -/
def Computes (p : MvPolynomial σ F) (s : ℕ) : Prop :=
  ∃ l : ℕ → MvPolynomial σ F, (∀ k < s, IsStep l k) ∧ ∃ k < s, l k = p

end Circuits

variable {F : Type*} [Field F] {σ : Type*} {s : ℕ}

section Proof

/-- `p` along the line through 0 and `u`. -/
noncomputable def line (u : σ → F) : MvPolynomial σ F →ₐ[F] Polynomial F :=
  MvPolynomial.aeval fun l => Polynomial.C (u l) * Polynomial.X

theorem eval_one_line (u : σ → F) (p : MvPolynomial σ F) :
    (line u p).eval 1 = MvPolynomial.eval u p := by
  have : ((Polynomial.evalRingHom (1 : F)).comp (line u).toRingHom) =
      (MvPolynomial.eval u : MvPolynomial σ F →+* F) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [line]
    · intro i; simp [line]
  exact DFunLike.congr_fun this p

end Proof

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Affine substitutions and the generic permanent

Entries that are affine in one variable, the generic permanent, and circuits under affine substitutions.
-/

namespace Nc

open Finset MvPolynomial

variable {F : Type*} [Field F]
variable {ι α θ : Type*} [Fintype ι] [Fintype α] [Fintype θ] [DecidableEq ι] [DecidableEq α] [DecidableEq θ]

/-- Constant, or affine in one variable. -/
def IsAffine (p : MvPolynomial ι F) : Prop := (∃ b, p = C b) ∨ ∃ i a b, p = C a * X i + C b

section Proof

/-- The constants and, for `some i`, the span of the constants and `X i`. -/
noncomputable def affIn (o : Option ι) : Submodule F (MvPolynomial ι F) :=
  match o with
  | none => Submodule.span F {1}
  | some i => Submodule.span F {X i, 1}

omit [Fintype ι] [DecidableEq ι] in
theorem one_mem_affIn (o : Option ι) : (1 : MvPolynomial ι F) ∈ affIn (F := F) o := by
  cases o
  · exact Submodule.subset_span rfl
  · exact Submodule.subset_span (by simp)

omit [Fintype ι] [DecidableEq ι] in
theorem C_mem_affIn (o : Option ι) (b : F) : (C b : MvPolynomial ι F) ∈ affIn (F := F) o := by
  have := (affIn (F := F) o).smul_mem b (one_mem_affIn o)
  rwa [MvPolynomial.smul_eq_C_mul, mul_one] at this

omit [Fintype ι] [DecidableEq ι] in
theorem isAffine_of_mem {o : Option ι} {p : MvPolynomial ι F} (h : p ∈ affIn (F := F) o) : IsAffine p := by
  cases o with
  | none =>
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 h
    exact Or.inl ⟨b, by rw [MvPolynomial.smul_eq_C_mul, mul_one]⟩
  | some i =>
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 h
    exact Or.inr ⟨i, a, b, by rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, mul_one]⟩

end Proof

section Circuits

/-- The permanent of the generic matrix. -/
noncomputable def genPerm (F : Type*) [Field F] (S : ℕ) : MvPolynomial (Fin S × Fin S) F :=
  (Matrix.of fun i j => X (i, j) : Matrix (Fin S) (Fin S) (MvPolynomial (Fin S × Fin S) F)).permanent

omit [Fintype ι] [DecidableEq ι] in
theorem aeval_genPerm {S : ℕ} (M : Matrix (Fin S) (Fin S) (MvPolynomial ι F)) :
    aeval (fun p : Fin S × Fin S => M p.1 p.2) (genPerm F S) = M.permanent := by
  simp [genPerm, Matrix.permanent, map_sum, map_prod]

omit [Fintype ι] [DecidableEq ι] in
/-- Substituting affine polynomials into a circuit costs a factor 5. -/
theorem Computes.aeval {κ : Type*} {p : MvPolynomial κ F} {s : ℕ} (h : Computes p s)
    (E : κ → MvPolynomial ι F) (hE : ∀ k, IsAffine (E k)) : Computes (MvPolynomial.aeval E p) (5 * s) := by
  obtain ⟨l, hl, k, hk, rfl⟩ := h
  have hblock : ∀ n, n < s → ∃ b : ℕ → MvPolynomial ι F, b 4 = MvPolynomial.aeval E (l n) ∧
      ∀ m : ℕ → MvPolynomial ι F, (∀ i < n, m (5 * i + 4) = MvPolynomial.aeval E (l i)) →
        (∀ t < 5, m (5 * n + t) = b t) → ∀ t < 5, IsStep m (5 * n + t) := by
    intro n hn
    have hconst : ∀ a : F, ∃ b : ℕ → MvPolynomial ι F, b 4 = C a ∧
      ∀ m : ℕ → MvPolynomial ι F, (∀ i < n, m (5 * i + 4) = MvPolynomial.aeval E (l i)) →
        (∀ t < 5, m (5 * n + t) = b t) → ∀ t < 5, IsStep m (5 * n + t) := fun a =>
      ⟨fun _ => C a, rfl, fun m _ hb t ht => Or.inr (Or.inl ⟨a, hb t ht⟩)⟩
    rcases hl n hn with ⟨x, hx⟩ | ⟨a, ha⟩ | ⟨i, hi, j, hj, e⟩ | ⟨i, hi, j, hj, e⟩
    · rw [hx, aeval_X]
      rcases hE x with ⟨b, hb⟩ | ⟨i, a, b, hab⟩
      · rw [hb]
        exact hconst b
      · rw [hab]
        refine ⟨fun t => if t = 0 then C a else if t = 1 then X i else if t = 2 then C a * X i else
          if t = 3 then C b else C a * X i + C b, rfl, fun m _ hm t ht => ?_⟩
        have h0 := hm 0 (by omega)
        have h1 := hm 1 (by omega)
        have h2 := hm 2 (by omega)
        have h3 := hm 3 (by omega)
        have h4 := hm 4 (by omega)
        simp only [if_true, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, if_false, one_ne_zero,
          Nat.reduceEqDiff] at h0 h1 h2 h3 h4
        interval_cases t
        · exact Or.inr (Or.inl ⟨a, h0⟩)
        · exact Or.inl ⟨i, h1⟩
        · exact Or.inr (Or.inr (Or.inr ⟨5 * n + 0, by omega, 5 * n + 1, by omega, by rw [h0, h1, h2]⟩))
        · exact Or.inr (Or.inl ⟨b, h3⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨5 * n + 2, by omega, 5 * n + 3, by omega, by rw [h2, h3, h4]⟩))
    · rw [ha, algHom_C]
      exact hconst a
    · refine ⟨fun t => if t = 4 then MvPolynomial.aeval E (l n) else 0, rfl, fun m hprev hm t ht => ?_⟩
      by_cases h4 : t = 4
      · subst h4
        refine Or.inr (Or.inr (Or.inl ⟨5 * i + 4, by omega, 5 * j + 4, by omega, ?_⟩))
        have h4 : m (5 * n + 4) = MvPolynomial.aeval E (l n) := hm 4 (by omega)
        rw [h4, hprev i hi, hprev j hj, e, map_add]
      · exact Or.inr (Or.inl ⟨0, (hm t ht).trans ((if_neg h4).trans (map_zero C).symm)⟩)
    · refine ⟨fun t => if t = 4 then MvPolynomial.aeval E (l n) else 0, rfl, fun m hprev hm t ht => ?_⟩
      by_cases h4 : t = 4
      · subst h4
        refine Or.inr (Or.inr (Or.inr ⟨5 * i + 4, by omega, 5 * j + 4, by omega, ?_⟩))
        have h4 : m (5 * n + 4) = MvPolynomial.aeval E (l n) := hm 4 (by omega)
        rw [h4, hprev i hi, hprev j hj, e, map_mul]
      · exact Or.inr (Or.inl ⟨0, (hm t ht).trans ((if_neg h4).trans (map_zero C).symm)⟩)
  choose! b hb4 hb using hblock
  refine ⟨fun q => b (q / 5) (q % 5), fun q hq => ?_, 5 * k + 4, by omega, ?_⟩
  · have hlt : q % 5 < 5 := Nat.mod_lt _ (by omega)
    have := hb (q / 5) (by omega) (fun q => b (q / 5) (q % 5)) (fun i hi => ?_) (fun t ht => ?_) (q % 5) hlt
    · rwa [Nat.div_add_mod] at this
    · have e1 : (5 * i + 4) / 5 = i := by omega
      have e2 : (5 * i + 4) % 5 = 4 := by omega
      simp only [e1, e2]
      exact hb4 i (by omega)
    · have e1 : (5 * (q / 5) + t) / 5 = q / 5 := by omega
      have e2 : (5 * (q / 5) + t) % 5 = t := by omega
      simp only [e1, e2]
  · have e1 : (5 * k + 4) / 5 = k := by omega
    have e2 : (5 * k + 4) % 5 = 4 := by omega
    simp only [e1, e2]
    exact hb4 k hk

end Circuits

end Nc
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Definitions for the quantitative theorem

Approximate circuits; families of polynomials that are complete for grid sums (the permanent, the Hamiltonian cycle
polynomial); the exponent of a unit tensor; sums of restrictions up to ε.
-/

namespace Nc

open Finset MvPolynomial

section Approx

variable {F X : Type*} [Field F]

/-- `f` is approximated by a circuit with at most `s` gates: a circuit over the Laurent series in ε computes some
`f + ε * g`, every coefficient of `g` being a power series. -/
def Approximates (f : MvPolynomial X F) (s : ℕ) : Prop :=
  ∃ p : MvPolynomial X (LaurentSeries F), Computes p s ∧
    ∀ (d : X →₀ ℕ) (i : ℤ), i ≤ 0 → (coeff d p).coeff i = if i = 0 then coeff d f else 0

end Approx

/-- The Hamiltonian cycle polynomial: the sum over the permutations with one cycle through all points. -/
noncomputable def genHC (F : Type*) [CommSemiring F] (m : ℕ) : MvPolynomial (Fin m × Fin m) F :=
  open Classical in ∑ σ : Equiv.Perm (Fin m) with σ.IsCycleOn Set.univ, ∏ i, X (i, σ i)

/-- The polynomials `G S`, one for every size `S`, are complete for grid sums with the blow-up `κ`: a sum over two
families of bits of a product of weights, one for every incidence, each affine in the variable of its incidence, is a
projection with affine entries of `G S` for all `S ≥ κ * #incidences`. -/
def GridComplete (F : Type) [Field F] (G : ∀ S : ℕ, MvPolynomial (Fin S × Fin S) F) (κ : ℕ) : Prop :=
  ∀ {ι N V W' : Type} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V] [Fintype W'] [DecidableEq W']
    (v : N → V) (w : N → W'), Function.Surjective v → Function.Surjective w →
    ∀ (W : N → Bool → Bool → MvPolynomial ι F) (o : W' → Option ι),
    (∀ n x r, W n x r ∈ affIn (F := F) (o (w n))) → ∀ S : ℕ, κ * Fintype.card N ≤ S →
    ∃ M : Fin S × Fin S → MvPolynomial ι F, (∀ q, IsAffine (M q)) ∧
      aeval M (G S) = ∑ x : V → Bool, ∑ r : W' → Bool, ∏ n, W n (x (v n)) (r (w n))

end Nc

namespace Nc.Price

open Ov Finset

variable {K : Type} [Field K] {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]

/-- The exponent g of the unit tensor with a leg at `π a` for every `a`: a spectral point has the value n ^ g at the
one of size n. -/
noncomputable def hexp (F : Spec K I) (π : A → I) : ℝ :=
  Real.logb 2 (F.F (Ten.push π (Ten.unit K A 2)))

/-- `t` is a sum of restrictions of the `b k` up to ε, with denominators at most ε ^ D: with local maps that are
polynomials in ε, the sum is ε ^ D * t + ε ^ (D + 1) * (anything). For D = 0 constant maps give the exact relation. -/
def BSum {κ : Type} [Fintype κ] (D : ℕ) (t : Ten K I) (b : κ → Ten K I) : Prop :=
  ∃ L : ∀ k p, t.ι p → (b k).ι p → Polynomial K, ∀ x, ∀ i ≤ D,
    (∑ k, ∑ y : ∀ p, (b k).ι p, (∏ p, L k p (x p) (y p)) * Polynomial.C ((b k).val y)).coeff i =
      if i = D then t.val x else 0

end Nc.Price
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Tensors, prices and duality": tensors

The subsection "Tensors". One theorem for every numbered statement, in the order of the paper and named by its label, and
one for every step of the running text that is used later. Tensors are arrays over a field K with one finite index set for
each party (Ov.Ten); tensors that are restrictions of one another (Ov.Ten.Equi) are not identified, instead a spectral point
has the same value on them (def_spectral_congr). The other subsections are in Paper/Gauges.lean, Paper/Extension.lean and
Paper/Prices.lean.
-/

namespace Paper

open Ov Ov.Ten Nc.Price Finset

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-! ## Tensors -/

section Tensors

variable {J L : Type} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- "Tensors that are restrictions of each other are identified, so that the product is commutative, with unit the tensor
1"; it is also associative. -/
theorem tensor_mul_laws (s t u : Ten K I) :
    Equi (s * t) (t * s) ∧ Equi (s * t * u) (s * (t * u)) ∧ Equi (1 * t) t ∧ Equi (t * 1) t :=
  ⟨Equi.mul_comm s t, Equi.mul_assoc s t u, Equi.one_mul t, Equi.mul_one t⟩

/-- "Every nonzero t has 1 as a restriction". -/
theorem tensor_one_restr [Nonempty I] {t : Ten K I} (ht : ∃ x, t.val x ≠ 0) : Restr 1 t :=
  Restr.one_le ht.choose_spec

/-- "Every t is covered by finitely many copies of 1." -/
theorem tensor_covered_by_ones [Nonempty I] (t : Ten K I) : ∃ r : ℕ, SumRestr t fun _ : Fin r => (1 : Ten K I) :=
  ⟨_, (rankLE_card t).sumRestr⟩

/-- "Push-forward commutes with products". -/
theorem tensor_push_mul (π : J → I) (s t : Ten K J) : Equi (Ten.push π (s * t)) (Ten.push π s * Ten.push π t) :=
  Equi.push_mul π s t

/-- "Push-forward commutes with … compositions". -/
theorem tensor_push_comp (π : J → I) (ρ : L → J) (t : Ten K L) :
    Equi (Ten.push π (Ten.push ρ t)) (Ten.push (π ∘ ρ) t) :=
  Equi.push_push π ρ t

/-- The push-forward along the identity does nothing. -/
theorem tensor_push_id (t : Ten K I) : Equi (Ten.push id t) t := Equi.push_id t

/-- "Push-forward … sends 1 to 1". -/
theorem tensor_push_one (π : J → I) : Equi (Ten.push π (1 : Ten K J)) 1 := Equi.push_one π

/-- "Push-forward … sends … covers to covers"; in particular restrictions to restrictions. -/
theorem tensor_push_cover (π : J → I) :
    (∀ {κ : Type} [Fintype κ] {s : Ten K J} {b : κ → Ten K J}, SumRestr s b →
      SumRestr (Ten.push π s) fun k => Ten.push π (b k)) ∧
    ∀ {s t : Ten K J}, Restr s t → Restr (Ten.push π s) (Ten.push π t) :=
  ⟨fun h => h.push π, fun h => h.push π⟩

end Tensors

/-- **Paper: Definition def:spectral.** "A spectral point on I is a function φ ≥ 0 on tensors with φ(1) = 1,
φ(st) = φ(s)φ(t), and φ(s) ≤ ∑ φ(t_j) whenever s is covered by t_1, …, t_r." -/
theorem def_spectral (φ : Ten K I → ℝ) :
    (∃ F : Spec K I, F.F = φ) ↔ (∀ t, 0 ≤ φ t) ∧ φ 1 = 1 ∧ (∀ s t, φ (s * t) = φ s * φ t) ∧
      ∀ (r : ℕ) (s : Ten K I) (t : Fin r → Ten K I), SumRestr s t → φ s ≤ ∑ j, φ (t j) := by
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨F.nonneg, F.one, F.mul, fun r s t h => F.le_sum s t h⟩
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨⟨φ, h0, h1, h2, fun {κ} _ s b h => ?_⟩, rfl⟩
    classical
    refine (h3 _ s (b ∘ (Fintype.equivFin κ).symm) (h.reindex (Fintype.equivFin κ).symm)).trans (le_of_eq ?_)
    exact Fintype.sum_equiv (Fintype.equivFin κ).symm _ _ fun _ => rfl

/-- The text after the definition: "So φ(t) ≥ 1 if t ≠ 0, and φ(0) = 0 (the empty sum)." -/
theorem def_spectral_values [Nonempty I] (φ : Spec K I) (t : Ten K I) :
    ((∃ x, t.val x ≠ 0) → 1 ≤ φ.F t) ∧ ((∀ x, t.val x = 0) → φ.F t = 0) :=
  ⟨fun ⟨_, hx⟩ => φ.one_le hx, φ.zero⟩

/-- Tensors that are restrictions of each other are identified: a spectral point is monotone under restriction, so it has
the same value on them. -/
theorem def_spectral_congr (φ : Spec K I) {s t : Ten K I} :
    (Restr s t → φ.F s ≤ φ.F t) ∧ (Equi s t → φ.F s = φ.F t) :=
  ⟨φ.mono, φ.congr⟩

open Classical in
/-- The first example after Definition def:spectral: "An example is φ(t) = 1 for all t ≠ 0". -/
noncomputable def trivialPoint (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] : Spec K I where
  F t := if ∃ x, t.val x ≠ 0 then 1 else 0
  nonneg t := by split_ifs <;> norm_num
  one := if_pos ⟨fun _ => (), one_ne_zero⟩
  mul s t := by
    by_cases hs : ∃ x, s.val x ≠ 0
    · by_cases ht : ∃ x, t.val x ≠ 0
      · rw [if_pos hs, if_pos ht, if_pos, mul_one]
        obtain ⟨x, hx⟩ := hs
        obtain ⟨y, hy⟩ := ht
        exact ⟨fun p => (x p, y p), mul_ne_zero hx hy⟩
      · rw [if_neg ht, mul_zero, if_neg]
        rintro ⟨x, hx⟩
        exact ht ⟨fun p => (x p).2, right_ne_zero_of_mul hx⟩
    · rw [if_neg hs, zero_mul, if_neg]
      rintro ⟨x, hx⟩
      exact hs ⟨fun p => (x p).1, left_ne_zero_of_mul hx⟩
  le_sum {κ} _ s b h := by
    by_cases hs : ∃ x, s.val x ≠ 0
    · rw [if_pos hs]
      obtain ⟨x, hx⟩ := hs
      obtain ⟨L, hL⟩ := h
      rw [hL] at hx
      obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
      have h1 : ∃ x, (b k).val x ≠ 0 := ⟨y, right_ne_zero_of_mul hy⟩
      calc (1 : ℝ) = if ∃ x, (b k).val x ≠ 0 then 1 else 0 := (if_pos h1).symm
        _ ≤ _ := Finset.single_le_sum
          (f := fun k => if ∃ x, (b k).val x ≠ 0 then (1 : ℝ) else 0)
          (fun k _ => by split_ifs <;> norm_num) (Finset.mem_univ k)
    · rw [if_neg hs]
      exact Finset.sum_nonneg fun k _ => by split_ifs <;> norm_num

/-- The last example after Definition def:spectral: "φ^s is again a spectral point for 0 < s ≤ 1." -/
noncomputable def powerPoint (φ : Spec K I) (s : ℝ) (h0 : 0 < s) (h1 : s ≤ 1) : Spec K I where
  F t := φ.F t ^ s
  nonneg t := Real.rpow_nonneg (φ.nonneg t) s
  one := by rw [φ.one, Real.one_rpow]
  mul a b := by rw [φ.mul, Real.mul_rpow (φ.nonneg a) (φ.nonneg b)]
  le_sum {κ} _ a b h := by
    classical
    refine (Real.rpow_le_rpow (φ.nonneg a) (φ.le_sum a b h) h0.le).trans ?_
    have key : ∀ S : Finset κ, (∑ k ∈ S, φ.F (b k)) ^ s ≤ ∑ k ∈ S, φ.F (b k) ^ s := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp [Real.zero_rpow h0.ne']
      | insert k S hk ih =>
        rw [Finset.sum_insert hk, Finset.sum_insert hk]
        exact (Real.rpow_add_le_add_rpow (φ.nonneg _) (Finset.sum_nonneg fun _ _ => φ.nonneg _) h0.le h1).trans
          (by gcongr)
    exact key Finset.univ

/-- Proof of Lemma lem:exponents: "The function q ↦ φ(⟨q⟩_P) is at least 1, multiplicative and monotone, hence a power of q."
The unit tensor has a leg at π a for every a; the exponent is Nc.Price.hexp. -/
theorem lem_exponents_power [Nonempty I] (φ : Spec K I) {A : Type} [Fintype A] [DecidableEq A] (π : A → I) :
    0 ≤ hexp φ π ∧ ∀ q : ℕ, 1 ≤ q → φ.F (Ten.push π (Ten.unit K A q)) = (q : ℝ) ^ hexp φ π :=
  ⟨Real.logb_nonneg (by norm_num) (φ.one_le_unit π (by norm_num)), fun _ hq =>
    eq_rpow_of_mul_mono (fun n => φ.F (Ten.push π (Ten.unit K A n))) (fun _ h => φ.one_le_unit π h)
      (fun m n _ _ => by
        rw [(def_spectral_congr φ).2 ((Equi.unit_mul m n).push π), (def_spectral_congr φ).2 (tensor_push_mul _ _ _), φ.mul])
      (fun _ _ _ h => (def_spectral_congr φ).1 ((Restr.unit_mono h).push π)) _ hq⟩

/-- The case of a wire: φ(⟨q⟩_uv) = q ^ d_φ(u,v). -/
theorem lem_exponents_wire (φ : Spec K I) (u v : I) {q : ℕ} (hq : 1 ≤ q) :
    φ.F (Ten.wire K q u v) = (q : ℝ) ^ φ.e u v :=
  have : Nonempty I := ⟨u⟩
  (lem_exponents_power φ ![u, v]).2 q hq

theorem lem_exponents_wire_two (φ : Spec K I) (u v : I) : φ.F (Ten.wire K 2 u v) = 2 ^ φ.e u v := by
  have := lem_exponents_wire φ u v (q := 2) (by norm_num)
  exact_mod_cast this

/-- Proof of Lemma lem:exponents: "A wire of dimension q is covered by q copies of 1, so d_φ ≤ 1." (The cover and its
consequence φ(⟨q⟩_uv) ≤ q are Ov.Spec.unit_le.) Also d_φ ≥ 0, as for every exponent. -/
theorem lem_exponents_unit_interval (φ : Spec K I) (u v : I) : 0 ≤ φ.e u v ∧ φ.e u v ≤ 1 := by
  have : Nonempty I := ⟨u⟩
  refine ⟨(lem_exponents_power φ ![u, v]).1, ?_⟩
  have h : φ.F (Ten.wire K 2 u v) ≤ (2 : ℕ) := φ.unit_le ![u, v] 2
  rw [lem_exponents_wire_two] at h
  have h2 : (2 : ℝ) ^ φ.e u v ≤ 2 ^ (1 : ℝ) := by simpa using h
  exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h2

/-- "We put ⟨q⟩_uu = 1": a wire from u to u is a restriction of 1, so d_φ(u,u) = 0. -/
theorem lem_exponents_self (φ : Spec K I) (u : I) : φ.e u u = 0 := by
  have : Nonempty I := ⟨u⟩
  have h : φ.F (Ten.wire K 2 u u) = 1 := by
    refine le_antisymm ?_ (φ.one_le_unit ![u, u] (by norm_num))
    rw [← φ.one]
    exact (def_spectral_congr φ).1 (Restr.wire_self 2 u)
  rw [Spec.e, h, Real.logb_one]

/-- A wire has no direction. -/
theorem lem_exponents_symm (φ : Spec K I) (u v : I) : φ.e u v = φ.e v u := by
  rw [Spec.e, Spec.e, (def_spectral_congr φ).2 (Equi.wire_comm 2 u v)]

/-- Proof of Lemma lem:exponents: "Contracting the two indices at v shows that ⟨q⟩_uw is a restriction of ⟨q⟩_uv ⟨q⟩_vw". -/
theorem lem_exponents_contract (q : ℕ) (u v w : I) :
    Restr (Ten.wire K q u w) (Ten.wire K q u v * Ten.wire K q v w) :=
  Restr.wire_trans q u w v

/-- Proof of Lemma lem:exponents: "… this is the triangle inequality." -/
theorem lem_exponents_triangle (φ : Spec K I) (u v w : I) : φ.e u w ≤ φ.e u v + φ.e v w := by
  have h := φ.le_mul (lem_exponents_contract (K := K) 2 u v w)
  rw [lem_exponents_wire_two, lem_exponents_wire_two, lem_exponents_wire_two, ← Real.rpow_add (by norm_num)] at h
  exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h

/-- Proof of Lemma lem:exponents: "Identifying the indices at every vertex in the same way shows that ⟨q⟩_P is a restriction of
the product of the wires on the edges of the tree." The unit tensor has a leg at π p for every vertex p ∈ A; the edge e joins
a e and b e; of the graph only connectedness is used, in the form that a function to Fin q that is constant along edges is
constant. -/
theorem lem_exponents_tree {A E : Type} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype E] [DecidableEq E] (q : ℕ)
    (π : A → I) (a b : E → A) (hconn : ∀ f : A → Fin q, (∀ e, f (a e) = f (b e)) → ∀ p p', f p = f p') :
    Restr (Ten.push π (Ten.unit K A q)) (Ten.prod fun e => Ten.wire K q (π (a e)) (π (b e))) := by
  classical
  have key := Restr.of_edges π (ξ := fun o : Option A => o.elim (π (Classical.arbitrary A)) π) (Ten.unit K A q)
    (fun _ : E => Fin q) (fun e => some (a e)) (fun e => some (b e))
    (fun o x l => o.elim 1 fun p => ∏ e, if a e = p ∨ b e = p then (if l e = x p then (1 : K) else 0) else 1)
    (by
      rintro (_ | p) x x' l l' hx hl
      · rfl
      · refine Finset.prod_congr rfl fun e _ => ?_
        by_cases he : a e = p ∨ b e = p
        · have h2 : l e = l' e := hl e (he.imp (congrArg some) (congrArg some))
          have h3 : x p = x' p := hx p rfl
          rw [if_pos he, if_pos he, h2, h3]
        · rw [if_neg he, if_neg he])
    (by
      intro x
      refine Eq.trans ?_ (Fintype.sum_eq_single (fun e => (x (a e) : Fin q)) ?_).symm
      · rw [Fintype.prod_option]
        show _ = 1 * _
        rw [one_mul]
        by_cases h : ∀ i j, x i = x j
        · rw [Ten.unit_val_of h]
          refine (Finset.prod_eq_one fun p _ => Finset.prod_eq_one fun e _ => ?_).symm
          exact (ite_eq_right_iff.2 fun _ => if_pos (h (a e) p))
        · rw [Ten.unit_val_not h]
          obtain ⟨e, he⟩ : ∃ e, x (a e) ≠ x (b e) := by
            by_contra hne
            push Not at hne
            exact h (hconn x hne)
          refine (Finset.prod_eq_zero (Finset.mem_univ (b e)) (Finset.prod_eq_zero (Finset.mem_univ e) ?_)).symm
          exact (if_pos (Or.inr rfl)).trans (if_neg he)
      · intro l hl
        obtain ⟨e, he⟩ := Function.ne_iff.1 hl
        refine Finset.prod_eq_zero (Finset.mem_univ (some (a e))) (Finset.prod_eq_zero (Finset.mem_univ e) ?_)
        exact (if_pos (Or.inl rfl)).trans (if_neg he))
  simpa only [Fintype.card_fin, Option.elim_some] using key

/-- The consequence of lem_exponents_tree in exponents: g_φ(P) ≤ ∑ d_φ(e) over the edges. -/
theorem lem_exponents_tree_le [Nonempty I] (φ : Spec K I) {A E : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype E] [DecidableEq E] (π : A → I) (a b : E → A)
    (hconn : ∀ f : A → Fin 2, (∀ e, f (a e) = f (b e)) → ∀ p p', f p = f p') :
    hexp φ π ≤ ∑ e, φ.e (π (a e)) (π (b e)) := by
  rw [hexp, Real.logb_le_iff_le_rpow (by norm_num) (zero_lt_one.trans_le (φ.one_le_unit π (by norm_num)))]
  refine (φ.le_prod (lem_exponents_tree 2 π a b hconn)).trans (le_of_eq ?_)
  rw [Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact Finset.prod_congr rfl fun e _ => lem_exponents_wire_two φ _ _

/-- **Paper: Lemma lem:exponents.** "Let φ be a spectral point on I. For every nonempty P ⊆ I there is g_φ(P) ≥ 0 with
φ(⟨q⟩_P) = q ^ g_φ(P) for all q ≥ 1. The function d_φ(u,v) = g_φ({u,v}), d_φ(u,u) = 0, is a pseudometric with values in
[0,1], and g_φ(P) ≤ ∑ d_φ(e) over the edges of any tree on P." The function d_φ is Ov.Spec.e. -/
theorem lem_exponents [Nonempty I] (φ : Spec K I) :
    ∃ g : Finset I → ℝ,
      (∀ P : Finset I, P.Nonempty → 0 ≤ g P ∧
        ∀ q : ℕ, 1 ≤ q → φ.F (Ten.push (Subtype.val : P → I) (Ten.unit K P q)) = (q : ℝ) ^ g P) ∧
      (∀ u v, u ≠ v → φ.e u v = g {u, v}) ∧ (∀ u, φ.e u u = 0) ∧
      (∀ u v, φ.e u v = φ.e v u) ∧ (∀ u v w, φ.e u w ≤ φ.e u v + φ.e v w) ∧ (∀ u v, φ.e u v ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ (P : Finset I) (G : SimpleGraph P) [DecidableRel G.Adj], G.IsTree →
        g P ≤ ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => φ.e u v, fun _ _ => lem_exponents_symm φ _ _⟩ (e.map Subtype.val) := by
  classical
  refine ⟨fun P => hexp φ (Subtype.val : P → I), fun P _ =>
    ⟨(lem_exponents_power φ _).1, (lem_exponents_power φ _).2⟩,
    fun u v _ => ?_, lem_exponents_self φ, lem_exponents_symm φ, lem_exponents_triangle φ,
    lem_exponents_unit_interval φ, ?_⟩
  · show hexp φ ![u, v] = hexp φ (Subtype.val : ({u, v} : Finset I) → I)
    have h : Set.range ![u, v] = Set.range (Subtype.val : ({u, v} : Finset I) → I) := by
      simp only [Matrix.range_cons, Matrix.range_empty, Subtype.range_coe_subtype]
      ext x
      simp [or_comm]
    rw [hexp, hexp, (def_spectral_congr φ).2 (Ten.Equi.push_unit_congr _ _ h 2)]
  · intro P G _ hT
    have : Nonempty P := hT.connected.nonempty
    refine (lem_exponents_tree_le φ (Subtype.val : P → I) (E := G.edgeFinset)
      (fun e => e.1.out.1) (fun e => e.1.out.2) fun f hf p q => ?_).trans (le_of_eq ?_)
    · obtain ⟨w⟩ := hT.connected.preconnected p q
      induction w with
      | nil => rfl
      | @cons u v _ hadj _ ih =>
        refine Eq.trans ?_ ih
        have hmem : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.2 hadj
        have h1 : f (s(u, v) : Sym2 P).out.1 = f (s(u, v) : Sym2 P).out.2 := hf ⟨_, hmem⟩
        have h2 : (s((s(u, v) : Sym2 P).out.1, (s(u, v) : Sym2 P).out.2) : Sym2 P) = s(u, v) := Quot.out_eq _
        rcases Sym2.eq_iff.1 h2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at h1
        exacts [h1, h1.symm]
    · rw [← Finset.sum_coe_sort G.edgeFinset]
      refine Finset.sum_congr rfl fun e _ => ?_
      conv_rhs => rw [← Quot.out_eq e.1]
      rfl

end Paper
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Gauges on a commutative monoid with a covering relation

Let M be a commutative monoid (the tensors up to equivalence) with a relation "t is covered by the finite
family b" (t is a sum of restrictions of the members of b). A gauge is a function p ≥ 0 on M with p(1) = 1,
p(st) ≤ p(s)p(t), and p(t) ≤ ∑ p(b) whenever b covers t. This file has the definitions, infima of directed families of
gauges (`isPre_iInf`, `keeps_iInf`), and the first facts on the numbers a with p(tⁿ) ≤ C·aⁿ (`IsPre.rad`). The proof of
Proposition prop:gauge is in Paper/Gauges.lean.
-/

namespace Ov.Duality

variable {M : Type*} [CommMonoid M]

/-- A covering relation between elements and finite families of elements: reflexive, transitive,
and compatible with multiplication by an element. -/
structure Cover (M : Type*) [CommMonoid M] where
  /-- the element is covered by the family -/
  cov : ∀ {κ : Type} [Fintype κ], M → (κ → M) → Prop
  refl : ∀ t, cov t (fun _ : Unit => t)
  bind : ∀ {κ : Type} [Fintype κ] {μ : κ → Type} [∀ k, Fintype (μ k)] {t : M} {b : κ → M}
    {c : ∀ k, μ k → M}, cov t b → (∀ k, cov (b k) (c k)) → cov t (fun x : Σ k, μ k => c x.1 x.2)
  mul : ∀ {κ : Type} [Fintype κ] {t : M} {b : κ → M} (s : M), cov t b →
    cov (t * s) (fun k => b k * s)

/-- The function p is a gauge: p ≥ 0, p(1) = 1, submultiplicative,
and subadditive under covers. -/
structure IsPre (D : Cover M) (p : M → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ p t
  one : p 1 = 1
  mul_le : ∀ s t, p (s * t) ≤ p s * p t
  le_sum : ∀ {κ : Type} [Fintype κ] (t : M) (b : κ → M), D.cov t b → p t ≤ ∑ k, p (b k)

/-- The inequality p(tx) ≤ c·p(ty) for all t. -/
def Keeps (p : M → ℝ) (x y : M) (c : ℝ) : Prop := ∀ t, p (t * x) ≤ c * p (t * y)

variable {D : Cover M} {p : M → ℝ}

omit [CommMonoid M] in
/-- For finitely many elements, one member of a directed family is close to its infimum. -/
theorem le_iInf_add {ι : Type*} [Nonempty ι] {P : ι → M → ℝ} (dir : Directed (· ≥ ·) P)
    {q : M → ℝ} (hq : ∀ t, q t = ⨅ i, P i t) {ε : ℝ} (hε : 0 < ε) (b : Finset M) :
    ∃ i, ∀ t ∈ b, P i t ≤ q t + ε := by
  classical
  induction b using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | insert a b _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := exists_lt_of_ciInf_lt (show ⨅ i, P i a < q a + ε by rw [← hq]; linarith)
    obtain ⟨k, hki, hkj⟩ := dir i j
    refine ⟨k, fun t ht => ?_⟩
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact (hkj t).trans hj.le
    · exact (hki t).trans (hi t ht)

/-- A directed infimum of functions P i is a gauge if each of them is, where instead of
P i (st) ≤ P i (s)·P i (t) it is enough that P j (st) ≤ P i (s)·P i (t) for some j. -/
theorem isPre_iInf {ι : Type*} [Nonempty ι] {P : ι → M → ℝ} (dir : Directed (· ≥ ·) P)
    (nonneg : ∀ i t, 0 ≤ P i t) (one : ∀ i, P i 1 = 1)
    (mul_le : ∀ i s t, ∃ j, P j (s * t) ≤ P i s * P i t)
    (le_sum : ∀ i, ∀ {κ : Type} [Fintype κ] (t : M) (b : κ → M), D.cov t b →
      P i t ≤ ∑ k, P i (b k)) :
    IsPre D (fun t => ⨅ i, P i t) := by
  classical
  have bdd : ∀ t, BddBelow (Set.range fun i => P i t) := fun t =>
    ⟨0, by rintro _ ⟨i, rfl⟩; exact nonneg i t⟩
  have hle : ∀ i t, ⨅ j, P j t ≤ P i t := fun i t => ciInf_le (bdd t) i
  have h0 : ∀ t, 0 ≤ ⨅ i, P i t := fun t => le_ciInf fun i => nonneg i t
  refine ⟨h0, ?_, ?_, ?_⟩
  · simp [one]
  · intro s t
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set A := ⨅ i, P i s with hA
    set B := ⨅ i, P i t with hB
    have hA0 : 0 ≤ A := h0 s
    have hB0 : 0 ≤ B := h0 t
    obtain ⟨ε, hε, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε * (A + B + 1) ≤ δ := by
      refine ⟨min 1 (δ / (A + B + 1)), by positivity, min_le_left _ _, ?_⟩
      calc min 1 (δ / (A + B + 1)) * (A + B + 1) ≤ δ / (A + B + 1) * (A + B + 1) := by
            gcongr; exact min_le_right _ _
        _ = δ := by field_simp
    obtain ⟨i, hi⟩ := le_iInf_add dir (q := fun t => ⨅ i, P i t) (fun _ => rfl) hε {s, t}
    have h1 := hi s (by simp)
    have h2 := hi t (by simp)
    obtain ⟨j, hj⟩ := mul_le i s t
    have h3 : P i s * P i t ≤ (A + ε) * (B + ε) :=
      mul_le_mul h1 h2 (nonneg _ _) (by positivity)
    have h4 := hle j (s * t)
    nlinarith
  · intro κ _ t b hb
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set ε := δ / (Fintype.card κ + 1) with hεd
    have hε : 0 < ε := by positivity
    obtain ⟨i, hi⟩ := le_iInf_add dir (q := fun t => ⨅ i, P i t) (fun _ => rfl) hε
      (Finset.univ.image b)
    have h1 : ∑ k, P i (b k) ≤ ∑ k, ((⨅ i, P i (b k)) + ε) :=
      Finset.sum_le_sum fun k _ => hi _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    have h2 : (Fintype.card κ : ℝ) * ε ≤ δ := by
      rw [hεd, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    have h3 := (hle i t).trans (le_sum i t b hb)
    linarith

theorem keeps_iInf {ι : Type*} [Nonempty ι] {P : ι → M → ℝ} (nonneg : ∀ i t, 0 ≤ P i t)
    {x y : M} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, Keeps (P i) x y c) :
    Keeps (fun t => ⨅ i, P i t) x y c := by
  intro t
  rw [Real.mul_iInf_of_nonneg hc]
  refine le_ciInf fun i => (ciInf_le ⟨0, ?_⟩ i).trans (h i t)
  rintro _ ⟨i, rfl⟩
  exact nonneg i _

namespace IsPre

theorem pow_le (h : IsPre D p) (t : M) (n : ℕ) : p (t ^ n) ≤ p t ^ n := by
  induction n with
  | zero => simp [h.one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (h.mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (h.nonneg _))

/-- The numbers a > 0 for which there is a C with p(t^m) ≤ C·a^m for all m. Their infimum is the
spectral radius of p at t. -/
def rad (p : M → ℝ) (t : M) : Set ℝ := {a | 0 < a ∧ ∃ C : ℝ, ∀ m : ℕ, p (t ^ m) ≤ C * a ^ m}

theorem rad_const_pos (h : IsPre D p) {t : M} {a C : ℝ} (hC : ∀ m : ℕ, p (t ^ m) ≤ C * a ^ m) :
    1 ≤ C := by simpa [h.one] using hC 0

theorem rad_mono (h : IsPre D p) {t : M} {a b : ℝ} (ha : a ∈ rad p t) (hab : a ≤ b) :
    b ∈ rad p t := by
  obtain ⟨ha0, C, hC⟩ := ha
  have hC1 := h.rad_const_pos hC
  refine ⟨ha0.trans_le hab, C, fun m => (hC m).trans ?_⟩
  gcongr

theorem rad_bdd (p : M → ℝ) (t : M) : BddBelow (rad p t) := ⟨0, fun _ ha => ha.1.le⟩

theorem mem_rad (h : IsPre D p) (t : M) {δ : ℝ} (hδ : 0 < δ) : p t + δ ∈ rad p t :=
  ⟨by linarith [h.nonneg t], 1, fun m => by
    rw [one_mul]
    exact (h.pow_le t m).trans (pow_le_pow_left₀ (h.nonneg t) (by linarith) m)⟩

theorem mem_rad_of_lt (h : IsPre D p) {t : M} {a : ℝ} (ha : sInf (rad p t) < a) :
    a ∈ rad p t := by
  obtain ⟨b, hb, hba⟩ := exists_lt_of_csInf_lt ⟨_, h.mem_rad t one_pos⟩ ha
  exact h.rad_mono hb hba.le

/-- The bound for a product of powers, by the bounds for the powers. -/
theorem prod_bound (h : IsPre D p) (S : Finset M) (a C : M → ℝ)
    (ha : ∀ y, 0 < a y) (hC : ∀ y, ∀ m : ℕ, p (y ^ m) ≤ C y * a y ^ m) (e : M → ℕ) :
    p (∏ y ∈ S, y ^ e y) ≤ (∏ y ∈ S, C y) * ∏ y ∈ S, a y ^ e y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [h.one]
  | insert y S hy ih =>
    rw [Finset.prod_insert hy, Finset.prod_insert hy, Finset.prod_insert hy]
    have h1 := mul_le_mul (hC y (e y)) ih (h.nonneg _)
      (mul_nonneg (zero_le_one.trans (h.rad_const_pos (hC y))) (pow_nonneg (ha y).le _))
    calc _ ≤ _ := (h.mul_le _ _).trans h1
      _ = _ := by ring

end IsPre

end Ov.Duality
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Gauges as infima of weights

For an abstract commutative monoid with a covering relation: a function that is defined as the infimum of the weights of
certificates is a gauge, if certificates can be multiplied and added along covers. Used for Theorem thm:duality
(`Paper/Gauges.lean`) and Proposition prop:extend (`Paper/Extension.lean`).
-/

namespace Ov.Duality

open Finset

variable {M : Type*} [CommMonoid M] {D : Cover M}

theorem le_sInf_mul_sInf {S T : Set ℝ} (hS : S.Nonempty) (hT : T.Nonempty)
    (hS0 : ∀ a ∈ S, 0 ≤ a) (hT0 : ∀ b ∈ T, 0 ≤ b) {x : ℝ} (h : ∀ a ∈ S, ∀ b ∈ T, x ≤ a * b) :
    x ≤ sInf S * sInf T := by
  have key : ∀ {S : Set ℝ} (_ : S.Nonempty) {b : ℝ} (_ : 0 ≤ b), (∀ a ∈ S, x ≤ a * b) →
      x ≤ sInf S * b := by
    intro S hS b hb h
    rcases hb.eq_or_lt with rfl | hb
    · obtain ⟨a, ha⟩ := hS
      simpa using h a ha
    · rw [← div_le_iff₀ hb]
      exact le_csInf hS fun a ha => (div_le_iff₀ hb).2 (h a ha)
  rw [mul_comm]
  refine key hT (Real.sInf_nonneg hS0) fun b hb => ?_
  rw [mul_comm]
  exact key hS (hT0 b hb) fun a ha => h a ha b hb

/-- Let S t be sets of numbers ≥ 0, the weights of the certificates for t. Their infimum is a gauge
if certificates can be multiplied and put together along covers, 1 has a certificate of weight
1, and none of a weight below 1. -/
theorem isPre_sInf {S : M → Set ℝ} (hne : ∀ t, (S t).Nonempty) (h0 : ∀ t, ∀ w ∈ S t, 0 ≤ w)
    (h1 : (1 : ℝ) ∈ S 1) (h1' : ∀ w ∈ S 1, 1 ≤ w)
    (hmul : ∀ s t, ∀ a ∈ S s, ∀ b ∈ S t, a * b ∈ S (s * t))
    (hsum : ∀ {κ : Type} [Fintype κ] (t : M) (b : κ → M), D.cov t b → ∀ w : κ → ℝ,
      (∀ k, w k ∈ S (b k)) → ∃ w' ∈ S t, w' ≤ ∑ k, w k) :
    IsPre D (fun t => sInf (S t)) := by
  have bdd : ∀ t, BddBelow (S t) := fun t => ⟨0, fun _ hw => h0 t _ hw⟩
  refine ⟨fun t => Real.sInf_nonneg (h0 t), ?_, ?_, ?_⟩
  · exact le_antisymm (csInf_le (bdd 1) h1) (le_csInf (hne 1) h1')
  · intro s t
    exact le_sInf_mul_sInf (hne s) (hne t) (h0 s) (h0 t) fun a ha b hb =>
      csInf_le (bdd _) (hmul s t a ha b hb)
  · intro κ _ t b hb
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set ε := δ / (Fintype.card κ + 1) with hεd
    have hε : 0 < ε := by positivity
    have hex : ∀ k, ∃ w ∈ S (b k), w < sInf (S (b k)) + ε := fun k =>
      exists_lt_of_csInf_lt (hne _) (by linarith)
    choose w hw hw' using hex
    obtain ⟨w', hw'S, hle⟩ := hsum t b hb w hw
    have h2 : ∑ k, w k ≤ ∑ k, (sInf (S (b k)) + ε) := Finset.sum_le_sum fun k _ => (hw' k).le
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    have h3 : (Fintype.card κ : ℝ) * ε ≤ δ := by
      rw [hεd, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    have h4 := csInf_le (bdd t) hw'S
    linarith

theorem keeps_sInf {S : M → Set ℝ} (hne : ∀ t, (S t).Nonempty) (h0 : ∀ t, ∀ w ∈ S t, 0 ≤ w)
    {x y : M} {c : ℝ} (hc : 0 < c) (h : ∀ t, ∀ w ∈ S (t * y), c * w ∈ S (t * x)) :
    Keeps (fun t => sInf (S t)) x y c := by
  intro t
  have h2 : sInf (S (t * x)) / c ≤ sInf (S (t * y)) := by
    refine le_csInf (hne _) fun a ha => ?_
    rw [div_le_iff₀ hc]
    exact (csInf_le ⟨0, fun _ hw => h0 _ _ hw⟩ (h t a ha)).trans (mul_comm _ _).le
  rw [div_le_iff₀ hc] at h2
  exact h2.trans (mul_comm _ _).le

/-- Covers can be multiplied. -/
theorem Cover.mul_mul (D : Cover M) {κ κ' : Type} [Fintype κ] [Fintype κ'] {s t : M} {b : κ → M}
    {c : κ' → M} (h : D.cov s b) (h' : D.cov t c) :
    D.cov (s * t) (fun x : Σ _ : κ, κ' => b x.1 * c x.2) := by
  refine D.bind (b := fun k => b k * t) (c := fun k j => b k * c j) (D.mul t h) fun k => ?_
  have := D.mul (b k) h'
  simpa only [mul_comm _ (b k)] using this

end Ov.Duality
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Gauges

A gauge (in Lean: `PreSpec`) is what a spectral point becomes when "multiplicative"
is weakened to "submultiplicative". Such a function is easy to write down, as an infimum over
certificates; `Paper.prop_gauge` finds a spectral point below it.
(Paper: the subsection "Gauges". The zero tensor is covered by the empty family, so a gauge is 0 at it.)
-/

namespace Ov

/-- A gauge on the parties I: a real function p ≥ 0 on tensors with p(1) = 1,
p(st) ≤ p(s)p(t), and p(s) ≤ ∑ p(b k) whenever s is a sum of restrictions of the b k. -/
structure PreSpec (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] where
  p : Ten K I → ℝ
  nonneg : ∀ t, 0 ≤ p t
  one : p 1 = 1
  mul_le : ∀ s t, p (s * t) ≤ p s * p t
  le_sum : ∀ {κ : Type} [Fintype κ] (s : Ten K I) (b : κ → Ten K I), Ten.SumRestr s b →
    p s ≤ ∑ k, p (b k)

namespace PreSpec

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- A gauge is monotone under restriction. -/
theorem mono (P : PreSpec K I) {s t : Ten K I} (h : Ten.Restr s t) : P.p s ≤ P.p t := by
  obtain ⟨L, hL⟩ := h
  have h1 : Ten.SumRestr s (fun _ : Unit => t) := ⟨fun _ => L, fun x => by simpa using hL x⟩
  simpa using P.le_sum s _ h1

end PreSpec

end Ov
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Tensors up to equivalence

Tensors that are restrictions of one another are identified; their classes form a commutative monoid with a covering
relation (`Ov.Duality.Abstract`). The proofs of Proposition prop:gauge and Theorem thm:duality (`Paper/Gauges.lean`) and of
Proposition prop:extend (`Paper/Extension.lean`) work there.
-/

namespace Ov

open Finset Duality

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

namespace Duality

/-- Tensors up to equivalence. -/
def tenSetoid (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] : Setoid (Ten K I) where
  r := Ten.Equi
  iseqv := ⟨Ten.Equi.refl, Ten.Equi.symm, Ten.Equi.trans⟩

/-- The classes of tensors over I under equivalence. -/
def Cls (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] : Type 1 :=
  Quotient (tenSetoid K I)

/-- The class of a tensor. -/
def cls (t : Ten K I) : Cls K I := Quotient.mk (tenSetoid K I) t

theorem cls_eq {s t : Ten K I} : cls s = cls t ↔ Ten.Equi s t :=
  ⟨fun h => Quotient.exact (s := tenSetoid K I) h, fun h => Quotient.sound (s := tenSetoid K I) h⟩

/-- A tensor of a given class. -/
noncomputable def rep (m : Cls K I) : Ten K I := Quotient.out (s := tenSetoid K I) m

@[simp] theorem cls_rep (m : Cls K I) : cls (rep m) = m := Quotient.out_eq _

theorem rep_cls (t : Ten K I) : Ten.Equi (rep (cls t)) t := cls_eq.1 (cls_rep _)

/-- The classes form a commutative monoid under the product. -/
noncomputable instance : CommMonoid (Cls K I) where
  one := cls 1
  mul x y := cls (rep x * rep y)
  mul_assoc x y z := by
    refine cls_eq.2 ?_
    exact (((rep_cls _).mul (Ten.Equi.refl _)).trans (Ten.Equi.mul_assoc _ _ _)).trans
      ((Ten.Equi.refl _).mul (rep_cls _).symm)
  one_mul x := by
    conv_rhs => rw [← cls_rep x]
    exact cls_eq.2 (((rep_cls _).mul (Ten.Equi.refl _)).trans (Ten.Equi.one_mul _))
  mul_one x := by
    conv_rhs => rw [← cls_rep x]
    exact cls_eq.2 (((Ten.Equi.refl _).mul (rep_cls _)).trans (Ten.Equi.mul_one _))
  mul_comm x y := cls_eq.2 (Ten.Equi.mul_comm _ _)

theorem cls_one : cls (1 : Ten K I) = 1 := rfl

theorem cls_mul (s t : Ten K I) : cls (s * t) = cls s * cls t :=
  cls_eq.2 ((rep_cls s).symm.mul (rep_cls t).symm)

theorem cls_kpow (t : Ten K I) (n : ℕ) : cls (Ten.kpow t n) = cls t ^ n := by
  induction n with
  | zero => rw [pow_zero, ← cls_one]; exact cls_eq.2 (Ten.Equi.kpow_zero t)
  | succ n ih => rw [pow_succ', ← ih, ← cls_mul]; exact cls_eq.2 (Ten.Equi.kpow_succ t n)

/-- The covering relation on classes: sums of restrictions. -/
noncomputable def tenCover (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] :
    Cover (Cls K I) where
  cov t b := Ten.SumRestr (rep t) (fun k => rep (b k))
  refl t := (Ten.Restr.refl _).sumRestr
  bind h h' := h.bind h'
  mul {κ _ t b} s h := by
    have h1 : Ten.SumRestr (rep t * rep s) (fun k => rep (b k) * rep s) := by
      have h2 := (h.mul (Ten.Restr.refl (rep s)).sumRestr).reindex (Equiv.prodPUnit κ).symm
      exact h2
    exact ((rep_cls _).1.trans_sum h1).mono fun k => (rep_cls _).2

theorem tenCover_cov {κ : Type} [Fintype κ] {t : Ten K I} {b : κ → Ten K I} :
    (tenCover K I).cov (cls t) (fun k => cls (b k)) ↔ Ten.SumRestr t b :=
  ⟨fun h => ((rep_cls t).2.trans_sum h).mono fun k => (rep_cls (b k)).1,
    fun h => ((rep_cls t).1.trans_sum h).mono fun k => (rep_cls (b k)).2⟩

/-- Equivalent tensors have the same value. -/
theorem _root_.Ov.PreSpec.congr (P : PreSpec K I) {s t : Ten K I} (h : Ten.Equi s t) :
    P.p s = P.p t := le_antisymm (P.mono h.1) (P.mono h.2)

/-- A gauge as a function on classes. -/
noncomputable def onCls (P : PreSpec K I) (m : Cls K I) : ℝ := P.p (rep m)

@[simp] theorem onCls_cls (P : PreSpec K I) (t : Ten K I) : onCls P (cls t) = P.p t :=
  P.congr (rep_cls t)

theorem isPre_onCls (P : PreSpec K I) : IsPre (tenCover K I) (onCls P) where
  nonneg _ := P.nonneg _
  one := by rw [← cls_one, onCls_cls, P.one]
  mul_le s t := by
    rw [← cls_rep s, ← cls_rep t, ← cls_mul, onCls_cls, onCls_cls, onCls_cls]
    exact P.mul_le _ _
  le_sum t b h := P.le_sum _ _ h

/-- The gauge given by a function on classes. -/
def ofCls {q : Cls K I → ℝ} (h : IsPre (tenCover K I) q) : PreSpec K I where
  p t := q (cls t)
  nonneg _ := h.nonneg _
  one := h.one
  mul_le s t := by rw [cls_mul]; exact h.mul_le _ _
  le_sum s b hb := h.le_sum _ _ (tenCover_cov.2 hb)

theorem keeps_onCls {P : PreSpec K I} {x y : Ten K I} {c : ℝ} (h : ∀ t, P.p (t * x) ≤ c * P.p (t * y)) :
    Duality.Keeps (onCls P) (cls x) (cls y) c := by
  intro m
  rw [← cls_rep m, ← cls_mul, ← cls_mul, onCls_cls, onCls_cls]
  exact h _

end Duality

end Ov
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Certificates

For the proof of Theorem thm:duality (`Paper/Gauges.lean`), in a commutative monoid with a covering relation, with an
element C and a finite family of elements A β: certificates, their products and sums.
-/

namespace Nc.Price

open Ov Ov.Duality Finset

variable {M : Type*} [CommMonoid M] {D : Cover M} {B : Type} [Fintype B]

/-- A product of the members of a family. -/
def mon (A : B → M) (v : B → ℕ) : M := ∏ β, A β ^ v β

theorem mon_zero (A : B → M) : mon A (fun _ => 0) = 1 := by simp [mon]

theorem mon_add (A : B → M) (v w : B → ℕ) : mon A (fun β => v β + w β) = mon A v * mon A w := by
  simp [mon, pow_add, Finset.prod_mul_distrib]

theorem mon_single [DecidableEq B] (A : B → M) (β : B) (n : ℕ) :
    mon A (fun γ => if γ = β then n else 0) = A β ^ n := by
  rw [mon, Finset.prod_eq_single β]
  · simp
  · intro γ _ h
    simp [h]
  · simp

/-- A certificate of level k and weight at most W for t: t·C^k is covered by products
C^u·∏A^v with u + Σv = k, and the numbers η^(Σv) add up to at most W. -/
def Cert (D : Cover M) (C : M) (A : B → M) (η : ℝ) (t : M) (k : ℕ) (W : ℝ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (u : κ → ℕ) (v : κ → B → ℕ), (∀ j, u j + ∑ β, v j β = k) ∧
    D.cov (t * C ^ k) (fun j => C ^ u j * mon A (v j)) ∧ ∑ j, η ^ (∑ β, v j β) ≤ W

namespace Cert

variable {C : M} {A : B → M} {η : ℝ} {s t : M} {k l : ℕ} {W V : ℝ}

theorem nonneg (hη : 0 < η) (h : Cert D C A η t k W) : 0 ≤ W := by
  obtain ⟨κ, _, u, v, -, -, hW⟩ := h
  exact (Finset.sum_nonneg fun j _ => by positivity).trans hW

theorem one (k : ℕ) : Cert D C A η 1 k 1 :=
  ⟨Unit, inferInstance, fun _ => k, fun _ _ => 0, by simp,
    by simpa [mon_zero] using D.refl (C ^ k), by simp⟩

theorem mul (hη : 0 < η) (h : Cert D C A η s k W) (h' : Cert D C A η t l V) :
    Cert D C A η (s * t) (k + l) (W * V) := by
  have hW0 := h.nonneg hη
  obtain ⟨κ, _, u, v, hu, hc, hW⟩ := h
  obtain ⟨κ', _, u', v', hu', hc', hW'⟩ := h'
  refine ⟨Σ _ : κ, κ', inferInstance, fun x => u x.1 + u' x.2, fun x β => v x.1 β + v' x.2 β,
    fun x => ?_, ?_, ?_⟩
  · have h1 := hu x.1
    have h2 := hu' x.2
    rw [Finset.sum_add_distrib]
    dsimp only
    omega
  · have h1 := D.mul_mul hc hc'
    have e1 : s * t * C ^ (k + l) = s * C ^ k * (t * C ^ l) := by
      rw [pow_add]; exact mul_mul_mul_comm _ _ _ _
    rw [e1]
    convert h1 using 2 with x
    rw [mon_add, pow_add]
    exact mul_mul_mul_comm _ _ _ _
  · rw [Fintype.sum_sigma]
    calc ∑ j, ∑ j', η ^ (∑ β, (v j β + v' j' β)) =
        (∑ j, η ^ (∑ β, v j β)) * ∑ j', η ^ (∑ β, v' j' β) := by
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
          rw [← pow_add, Finset.sum_add_distrib]
      _ ≤ W * V := mul_le_mul hW hW' (Finset.sum_nonneg fun j _ => by positivity) hW0

theorem raise (hη : 0 < η) (h : Cert D C A η t k W) (hkl : k ≤ l) : Cert D C A η t l W := by
  have h1 := h.mul hη (one (D := D) (C := C) (A := A) (η := η) (l - k))
  rwa [mul_one, mul_one, Nat.add_sub_cancel' hkl] at h1

theorem cover {κ : Type} [Fintype κ] {b : κ → M} {W : κ → ℝ} (h : D.cov t b)
    (hb : ∀ j, Cert D C A η (b j) k (W j)) : Cert D C A η t k (∑ j, W j) := by
  choose μ i u v hu hc hW using hb
  refine ⟨Σ j, μ j, inferInstance, fun x => u x.1 x.2, fun x => v x.1 x.2,
    fun x => hu _ _, D.bind (b := fun j => b j * C ^ k) (D.mul _ h) hc, ?_⟩
  rw [Fintype.sum_sigma]
  exact Finset.sum_le_sum fun j _ => hW j

theorem mul_gen (hη : 0 < η) (β : B) (h : Cert D C A η (t * C) k W) :
    Cert D C A η (t * A β) (k + 1) (η * W) := by
  classical
  obtain ⟨κ, _, u, v, hu, hc, hW⟩ := h
  have hs : ∀ j, ∑ γ, (v j γ + if γ = β then 1 else 0) = ∑ γ, v j γ + 1 := fun j => by
    rw [Finset.sum_add_distrib]; simp
  refine ⟨κ, inferInstance, u, fun j γ => v j γ + if γ = β then 1 else 0,
    fun j => by have := hu j; rw [hs]; omega, ?_, ?_⟩
  · have h1 := D.mul (A β) hc
    have e1 : t * A β * C ^ (k + 1) = t * C * C ^ k * A β := by rw [pow_succ]; ac_rfl
    rw [e1]
    convert h1 using 2 with j
    rw [mon_add, mon_single, pow_one, mul_assoc]
  · calc ∑ j, η ^ (∑ γ, (v j γ + if γ = β then 1 else 0)) = η * ∑ j, η ^ (∑ γ, v j γ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [hs, ← pow_succ']
      _ ≤ η * W := by gcongr

end Cert

section Tensors

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

theorem cls_prod {κ : Type} [Fintype κ] [DecidableEq κ] (b : κ → Ten K I) :
    cls (Ten.prod b) = ∏ k, cls (b k) := by
  have key : ∀ {n : ℕ} (b : Fin n → Ten K I), cls (Ten.prod b) = ∏ k, cls (b k) := by
    intro n
    induction n with
    | zero => intro b; rw [Fin.prod_univ_zero, ← cls_one]; exact cls_eq.2 (Ten.Equi.prod_empty b)
    | succ n ih =>
      intro b
      rw [Fin.prod_univ_succ, ← ih, ← cls_mul]
      exact cls_eq.2 (Ten.Equi.prod_fin_succ b)
  rw [cls_eq.2 (Ten.Equi.prod_reindex b (Fintype.equivFin κ).symm), key]
  exact Fintype.prod_equiv (Fintype.equivFin κ).symm _ _ fun _ => rfl

theorem cls_mon [DecidableEq B] (A : B → Ten K I) (v : B → ℕ) :
    mon (fun β => cls (A β)) v = cls (Ten.prod fun β => Ten.kpow (A β) (v β)) := by
  rw [cls_prod]
  exact Finset.prod_congr rfl fun β _ => (cls_kpow _ _).symm

end Tensors

end Nc.Price
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Tensors, prices and duality": gauges and duality

The subsection "Gauges": Proposition prop:gauge and Theorem thm:duality, with the steps of their proofs. Both proofs are
carried out in the commutative monoid of the classes of tensors (Ov.Duality.Cls) with its covering relation.
-/

namespace Paper

open Ov Ov.Ten Ov.Duality Ov.Duality.IsPre Nc.Price Finset

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- "A gauge on I is a function p ≥ 0 on tensors with p(1) = 1, p(st) ≤ p(s)p(t) and p(s) ≤ ∑ p(t_j) whenever s is covered by
the t_j." -/
theorem def_gauge (p : Ten K I → ℝ) :
    (∃ P : PreSpec K I, P.p = p) ↔ (∀ t, 0 ≤ p t) ∧ p 1 = 1 ∧ (∀ s t, p (s * t) ≤ p s * p t) ∧
      ∀ (r : ℕ) (s : Ten K I) (t : Fin r → Ten K I), SumRestr s t → p s ≤ ∑ j, p (t j) := by
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P.nonneg, P.one, P.mul_le, fun r s t h => P.le_sum s t h⟩
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨⟨p, h0, h1, h2, fun {κ} _ s b h => ?_⟩, rfl⟩
    classical
    refine (h3 _ s (b ∘ (Fintype.equivFin κ).symm) (h.reindex (Fintype.equivFin κ).symm)).trans (le_of_eq ?_)
    exact Fintype.sum_equiv (Fintype.equivFin κ).symm _ _ fun _ => rfl

section Monoid

/-! The proof of Proposition prop:gauge, for a commutative monoid M with a covering relation D (for us: the classes of
tensors). A gauge on M is a function with Ov.Duality.IsPre; Ov.Duality.Keeps p x y c says that p keeps (x, y, c). -/

variable {M : Type*} [CommMonoid M] {D : Cover M} {p : M → ℝ}

/-- Proof of Proposition prop:gauge: "The gauges below the given one that keep its triples are closed under infima of
chains." The infimum of a chain (or a directed family) of gauges is a gauge below them that keeps every triple which all
of them keep. -/
theorem prop_gauge_chain {ι : Type*} [Nonempty ι] {P : ι → M → ℝ} (dir : Directed (· ≥ ·) P)
    (hP : ∀ i, IsPre D (P i)) :
    IsPre D (fun t => ⨅ i, P i t) ∧ (∀ i t, ⨅ j, P j t ≤ P i t) ∧
      ∀ x y c, 0 ≤ c → (∀ i, Keeps (P i) x y c) → Keeps (fun t => ⨅ i, P i t) x y c :=
  ⟨isPre_iInf dir (fun i => (hP i).nonneg) (fun i => (hP i).one) (fun i s t => ⟨i, (hP i).mul_le s t⟩)
      (fun i _ _ t b hb => (hP i).le_sum t b hb),
    fun i t => ciInf_le ⟨0, by rintro _ ⟨j, rfl⟩; exact (hP j).nonneg t⟩ i,
    fun _ _ _ hc h => keeps_iInf (fun i => (hP i).nonneg) hc h⟩

/-- Proof of Proposition prop:gauge: "By Zorn's lemma there is a minimal one, p": a gauge below p₀ that keeps the triples of
p₀, and that is equal to every such gauge below it. -/
theorem prop_gauge_minimal {p₀ : M → ℝ} (h₀ : IsPre D p₀) :
    ∃ p : M → ℝ, IsPre D p ∧ (∀ t, p t ≤ p₀ t) ∧ (∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps p x y c) ∧
      ∀ q : M → ℝ, IsPre D q → (∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps q x y c) → (∀ t, q t ≤ p t) →
        ∀ t, q t = p t := by
  set Q : Set (M → ℝ)ᵒᵈ := {q | IsPre D (OrderDual.ofDual q) ∧
    ∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps (OrderDual.ofDual q) x y c} with hQ
  obtain ⟨m, hm0, hmax⟩ := zorn_le_nonempty₀ Q (by
    intro c hcQ hchain y hy
    have : Nonempty c := ⟨⟨y, hy⟩⟩
    obtain ⟨h1, h2, h3⟩ := prop_gauge_chain (D := D) (P := fun i : c => OrderDual.ofDual i.1) (by
      intro i j
      rcases hchain.total i.2 j.2 with hij | hij
      · exact ⟨j, hij, le_refl _⟩
      · exact ⟨i, le_refl _, hij⟩) fun i => (hcQ i.2).1
    exact ⟨OrderDual.toDual (fun t => ⨅ i : c, (OrderDual.ofDual i.1) t),
      ⟨h1, fun x y c hc hk => h3 x y c hc fun i => (hcQ i.2).2 x y c hc hk⟩, fun z hz t => h2 ⟨z, hz⟩ t⟩)
    (OrderDual.toDual p₀) ⟨h₀, fun _ _ _ _ hk => hk⟩
  refine ⟨OrderDual.ofDual m, hmax.1.1, hm0, hmax.1.2, fun q h1 h2 h3 t => ?_⟩
  have h4 : OrderDual.ofDual m ≤ q := hmax.2 (y := OrderDual.toDual q) ⟨h1, h2⟩ h3
  exact le_antisymm (h3 t) (h4 t)

/-- Proof of Proposition prop:gauge, for r(t) = inf p(tⁿ)^(1/n): "If s is covered by t_1, …, t_l, then sⁿ is covered by their
words of length n; grouping these … and bounding p(t_jᵃ) ≤ c_δ (r(t_j) + δ)ᵃ gives r(s) ≤ ∑ r(t_j)." In Lean r(t) is the infimum
of the a > 0 with p(tⁿ) ≤ C·aⁿ for some C and all n (Ov.Duality.IsPre.rad; it is the printed number by prop_gauge_radius_eq),
and the words are bounded by induction on n. -/
theorem prop_gauge_radius_cover (h : IsPre D p) {κ : Type} [Fintype κ] (t : M) (b : κ → M) (hb : D.cov t b) :
    sInf (rad p t) ≤ ∑ k, sInf (rad p (b k)) := by
  classical
  have h0 : ∀ t, 0 ≤ sInf (rad p t) := fun t => Real.sInf_nonneg fun _ ha => ha.1.le
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε := δ / (Fintype.card κ + 1) with hεd
  have hε : 0 < ε := by positivity
  set a : M → ℝ := fun y => sInf (rad p y) + ε with ha
  have ha0 : ∀ y, 0 < a y := fun y => by have := h0 y; simp only [ha]; linarith
  have hmem : ∀ y, ∃ C : ℝ, ∀ m : ℕ, p (y ^ m) ≤ C * a y ^ m := fun y =>
    (h.mem_rad_of_lt (show sInf (rad p y) < a y by simp only [ha]; linarith)).2
  choose C hC using hmem
  set S := Finset.univ.image b with hS
  set A := ∑ k, a (b k) with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => (ha0 _).le
  have key : ∀ n : ℕ, ∀ e : M → ℕ, p ((∏ y ∈ S, y ^ e y) * t ^ n) ≤
      (∏ y ∈ S, C y) * (∏ y ∈ S, a y ^ e y) * A ^ n := by
    intro n
    induction n with
    | zero => intro e; simpa using h.prod_bound S a C ha0 hC e
    | succ n ih =>
      intro e
      have h1 := h.le_sum _ _ (D.mul ((∏ y ∈ S, y ^ e y) * t ^ n) hb)
      have h2 : t * ((∏ y ∈ S, y ^ e y) * t ^ n) = (∏ y ∈ S, y ^ e y) * t ^ (n + 1) := by
        rw [pow_succ', mul_left_comm]
      rw [h2] at h1
      refine h1.trans ?_
      have h3 : ∀ k, p (b k * ((∏ y ∈ S, y ^ e y) * t ^ n)) ≤
          (∏ y ∈ S, C y) * (∏ y ∈ S, a y ^ e y) * A ^ n * a (b k) := by
        intro k
        set y := b k with hy
        have hyS : y ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ _)
        have h4 := ih (fun z => if z = y then e z + 1 else e z)
        have e1 : ∏ z ∈ S, z ^ (if z = y then e z + 1 else e z) =
            y * ∏ z ∈ S, z ^ e z := by
          rw [← Finset.mul_prod_erase S _ hyS, ← Finset.mul_prod_erase S (fun z => z ^ e z) hyS]
          rw [if_pos rfl, pow_succ', mul_assoc]
          congr 2
          refine Finset.prod_congr rfl fun z hz => ?_
          rw [if_neg (Finset.ne_of_mem_erase hz)]
        have e2 : ∏ z ∈ S, a z ^ (if z = y then e z + 1 else e z) =
            a y * ∏ z ∈ S, a z ^ e z := by
          rw [← Finset.mul_prod_erase S _ hyS,
            ← Finset.mul_prod_erase S (fun z => a z ^ e z) hyS]
          rw [if_pos rfl, pow_succ', mul_assoc]
          congr 2
          refine Finset.prod_congr rfl fun z hz => ?_
          rw [if_neg (Finset.ne_of_mem_erase hz)]
        rw [e1, e2] at h4
        rw [← mul_assoc]
        refine h4.trans (le_of_eq ?_)
        ring
      refine (Finset.sum_le_sum fun k _ => h3 k).trans (le_of_eq ?_)
      rw [← Finset.mul_sum, ← hA]
      ring
  have h5 : sInf (rad p t) ≤ A + ε := by
    refine csInf_le (rad_bdd p t) ⟨by linarith, ∏ y ∈ S, C y, fun m => ?_⟩
    have h6 := key m (fun _ => 0)
    simp only [pow_zero, Finset.prod_const_one, one_mul, mul_one] at h6
    refine h6.trans ?_
    have : (0 : ℝ) ≤ ∏ y ∈ S, C y :=
      Finset.prod_nonneg fun y _ => zero_le_one.trans (h.rad_const_pos (hC y))
    gcongr
    linarith
  have h7 : A = ∑ k, sInf (rad p (b k)) + Fintype.card κ * ε := by
    rw [hA, ha, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h8 : ((Fintype.card κ : ℝ) + 1) * ε = δ := by rw [hεd]; field_simp
  linarith

/-- Proof of Proposition prop:gauge: r is a gauge. "Clearly r(1) = 1 and r(st) ≤ r(s)r(t)"; for covers see
prop_gauge_radius_cover. -/
theorem prop_gauge_radius (h : IsPre D p) : IsPre D (fun t => sInf (rad p t)) := by
  classical
  have h0 : ∀ t, 0 ≤ sInf (rad p t) := fun t => Real.sInf_nonneg fun _ ha => ha.1.le
  refine ⟨h0, le_antisymm ?_ ?_, ?_, fun t b hb => prop_gauge_radius_cover h t b hb⟩
  · refine le_of_forall_pos_le_add fun δ hδ => csInf_le (rad_bdd p 1) ?_
    simpa [h.one] using h.mem_rad 1 hδ
  · refine le_csInf ⟨_, h.mem_rad 1 one_pos⟩ ?_
    rintro a ⟨ha, C, hC⟩
    by_contra hlt
    rw [not_le] at hlt
    have hC1 := h.rad_const_pos hC
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / C by positivity) hlt
    have := hC m
    rw [one_pow, h.one] at this
    rw [lt_div_iff₀ (by positivity)] at hm
    linarith
  · intro s t
    have key : ∀ a ∈ rad p s, ∀ b ∈ rad p t, sInf (rad p (s * t)) ≤ a * b := by
      rintro a ⟨ha, C, hC⟩ b ⟨hb, C', hC'⟩
      refine csInf_le (rad_bdd p _) ⟨by positivity, C * C', fun m => ?_⟩
      rw [mul_pow, mul_pow]
      have h1 := h.rad_const_pos hC
      calc p (s ^ m * t ^ m) ≤ p (s ^ m) * p (t ^ m) := h.mul_le _ _
        _ ≤ (C * a ^ m) * (C' * b ^ m) :=
          mul_le_mul (hC m) (hC' m) (h.nonneg _) (by positivity)
        _ = _ := by ring
    have hs := h0 s
    have ht := h0 t
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set A := sInf (rad p s) with hA
    set B := sInf (rad p t) with hB
    obtain ⟨ε, hε, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε * (A + B + 1) ≤ δ := by
      refine ⟨min 1 (δ / (A + B + 1)), by positivity, min_le_left _ _, ?_⟩
      calc min 1 (δ / (A + B + 1)) * (A + B + 1) ≤ δ / (A + B + 1) * (A + B + 1) := by
            gcongr; exact min_le_right _ _
        _ = δ := by field_simp
    have := key (A + ε) (h.mem_rad_of_lt (by linarith)) (B + ε) (h.mem_rad_of_lt (by linarith))
    nlinarith

/-- Proof of Proposition prop:gauge: r ≤ p. -/
theorem prop_gauge_radius_le (h : IsPre D p) (t : M) : sInf (rad p t) ≤ p t :=
  le_of_forall_pos_le_add fun _ hδ => csInf_le (rad_bdd p t) (h.mem_rad t hδ)

/-- Proof of Proposition prop:gauge: "If p keeps (x, y, c), then p(tⁿxⁿ) ≤ cⁿ p(tⁿyⁿ), so r keeps it." -/
theorem prop_gauge_radius_keeps (h : IsPre D p) {x y : M} {c : ℝ} (hc : 0 ≤ c) (hk : Keeps p x y c) :
    Keeps (fun t => sInf (rad p t)) x y c := by
  intro t
  -- first p(s x^m) ≤ c^m p(s y^m) for all m and s
  have h1 : ∀ (m : ℕ) (s : M), p (s * x ^ m) ≤ c ^ m * p (s * y ^ m) := by
    intro m
    induction m with
    | zero => intro s; simp
    | succ m ih =>
      intro s
      calc p (s * x ^ (m + 1)) = p (s * x * x ^ m) := by rw [pow_succ', mul_assoc]
        _ ≤ c ^ m * p (s * x * y ^ m) := ih _
        _ = c ^ m * p (s * y ^ m * x) := by rw [mul_right_comm]
        _ ≤ c ^ m * (c * p (s * y ^ m * y)) := by gcongr; exact hk _
        _ = c ^ (m + 1) * p (s * y ^ (m + 1)) := by
          rw [mul_assoc s, ← pow_succ, pow_succ c m, mul_assoc]
  have h2 : ∀ a ∈ rad p (t * y), sInf (rad p (t * x)) ≤ c * a := by
    rintro a ⟨ha, C, hC⟩
    have hC1 := h.rad_const_pos hC
    refine le_of_forall_pos_le_add fun δ hδ => csInf_le (rad_bdd p _) ⟨by positivity, C, fun m => ?_⟩
    calc p ((t * x) ^ m) = p (t ^ m * x ^ m) := by rw [mul_pow]
      _ ≤ c ^ m * p (t ^ m * y ^ m) := h1 m _
      _ ≤ c ^ m * (C * a ^ m) := by rw [← mul_pow]; gcongr; exact hC m
      _ = C * (c * a) ^ m := by ring
      _ ≤ C * (c * a + δ) ^ m := by gcongr; linarith
  rcases hc.eq_or_lt with rfl | hc
  · simpa using h2 _ (h.mem_rad _ one_pos)
  · have h3 : sInf (rad p (t * x)) / c ≤ sInf (rad p (t * y)) := by
      refine le_csInf ⟨_, h.mem_rad _ one_pos⟩ fun a ha => ?_
      rw [div_le_iff₀ hc]
      exact (h2 a ha).trans (mul_comm _ _).le
    rw [div_le_iff₀ hc] at h3
    exact h3.trans (mul_comm _ _).le

/-- If p((tⁿ)ᵐ) ≤ C·aᵐ for all m, then p(tᵐ) ≤ C′·bᵐ for all m, with bⁿ = a. -/
theorem prop_gauge_radius_root (h : IsPre D p) {t : M} {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : a ∈ rad p (t ^ n)) :
    a ^ ((n : ℝ)⁻¹) ∈ rad p t := by
  obtain ⟨ha, C, hC⟩ := ha
  have hC1 := h.rad_const_pos hC
  set b := a ^ ((n : ℝ)⁻¹) with hb
  have hb0 : 0 < b := Real.rpow_pos_of_pos ha _
  have hbn : b ^ n = a := Real.rpow_inv_natCast_pow ha.le (by omega)
  set E := max 1 (p t / b) with hE
  have hE1 : 1 ≤ E := le_max_left _ _
  refine ⟨hb0, C * E ^ n, fun m => ?_⟩
  have h1 : t ^ m = (t ^ n) ^ (m / n) * t ^ (m % n) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h2 : b ^ m = a ^ (m / n) * b ^ (m % n) := by
    rw [← hbn, ← pow_mul, ← pow_add, Nat.div_add_mod]
  have h3 : p t ≤ E * b := by
    rw [← div_le_iff₀ hb0]; exact le_max_right _ _
  have h4 : p (t ^ (m % n)) ≤ E ^ n * b ^ (m % n) := by
    calc p (t ^ (m % n)) ≤ p t ^ (m % n) := h.pow_le _ _
      _ ≤ (E * b) ^ (m % n) := pow_le_pow_left₀ (h.nonneg t) h3 _
      _ = E ^ (m % n) * b ^ (m % n) := mul_pow _ _ _
      _ ≤ E ^ n * b ^ (m % n) := by
        gcongr
        exact (Nat.mod_lt _ hn).le
  rw [h1, h2]
  calc _ ≤ p ((t ^ n) ^ (m / n)) * p (t ^ (m % n)) := h.mul_le _ _
    _ ≤ (C * a ^ (m / n)) * (E ^ n * b ^ (m % n)) :=
      mul_le_mul (hC _) h4 (h.nonneg _) (by positivity)
    _ = _ := by ring

/-- Proof of Proposition prop:gauge: "Let r(t) = inf_{n≥1} p(tⁿ)^(1/n)". The number r(t) of the Lean proof, the infimum of the
a > 0 with p(tⁿ) ≤ C·aⁿ for some C and all n, is the printed one. (That r(t) + δ is such an a, Ov.Duality.IsPre.mem_rad_of_lt,
is the printed bound p(tᵃ) ≤ c_δ (r(t) + δ)ᵃ, which the paper takes from Fekete's lemma.) -/
theorem prop_gauge_radius_eq (h : IsPre D p) (t : M) :
    sInf (rad p t) = ⨅ n : ℕ, p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) := by
  have hbdd : BddBelow (Set.range fun n : ℕ => p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact Real.rpow_nonneg (h.nonneg _) _⟩
  refine le_antisymm (le_ciInf fun n => ?_) (le_csInf ⟨_, h.mem_rad t one_pos⟩ ?_)
  · -- (p(tⁿ) + δ)^(1/n) is such an a, for every δ > 0
    have h1 : ∀ δ : ℝ, 0 < δ → sInf (rad p t) ≤ (p (t ^ (n + 1)) + δ) ^ (((n + 1 : ℕ) : ℝ)⁻¹) := fun δ hδ =>
      csInf_le (rad_bdd p t) (prop_gauge_radius_root h n.succ_pos (h.mem_rad _ hδ))
    have h2 : Filter.Tendsto (fun δ : ℝ => (p (t ^ (n + 1)) + δ) ^ (((n + 1 : ℕ) : ℝ)⁻¹)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹))) := by
      have h3 : Continuous fun δ : ℝ => (p (t ^ (n + 1)) + δ) ^ (((n + 1 : ℕ) : ℝ)⁻¹) :=
        (Real.continuous_rpow_const (by positivity)).comp (continuous_const.add continuous_id)
      have h4 := h3.tendsto 0
      rw [add_zero] at h4
      exact h4.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto h2 (Filter.eventually_of_mem self_mem_nhdsWithin fun δ hδ => h1 δ hδ)
  · -- p(tⁿ)^(1/n) ≤ C^(1/n)·a, and C^(1/n) tends to 1
    rintro a ⟨ha, C, hC⟩
    have hC1 := h.rad_const_pos hC
    have h1 : ∀ n : ℕ, ⨅ n : ℕ, p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) ≤ C ^ (((n + 1 : ℕ) : ℝ)⁻¹) * a := by
      intro n
      refine (ciInf_le hbdd n).trans ?_
      calc p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) ≤ (C * a ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) :=
            Real.rpow_le_rpow (h.nonneg _) (hC _) (by positivity)
        _ = C ^ (((n + 1 : ℕ) : ℝ)⁻¹) * a := by
          rw [Real.mul_rpow (by linarith) (by positivity), Real.pow_rpow_inv_natCast ha.le n.succ_ne_zero]
    have h2 : Filter.Tendsto (fun n : ℕ => C ^ (((n + 1 : ℕ) : ℝ)⁻¹) * a) Filter.atTop (nhds (C ^ (0 : ℝ) * a)) := by
      refine Filter.Tendsto.mul_const a ?_
      refine ((Real.continuous_const_rpow (by linarith : C ≠ 0)).tendsto 0).comp ?_
      exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
    rw [Real.rpow_zero, one_mul] at h2
    exact ge_of_tendsto' h2 h1

/-- Proof of Proposition prop:gauge: "r = p, that is, p(tⁿ) = p(t)ⁿ." -/
theorem prop_gauge_radius_pow (h : IsPre D p) (hr : ∀ t, sInf (rad p t) = p t) (t : M) (n : ℕ) :
    p (t ^ n) = p t ^ n := by
  refine le_antisymm (h.pow_le t n) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [h.one]
  rw [← hr (t ^ n)]
  refine le_csInf ⟨_, h.mem_rad _ one_pos⟩ fun a ha => ?_
  have h5 : p t ≤ a ^ ((n : ℝ)⁻¹) := by
    rw [← hr t]
    exact csInf_le (rad_bdd p t) (prop_gauge_radius_root h hn ha)
  calc p t ^ n ≤ (a ^ ((n : ℝ)⁻¹)) ^ n := pow_le_pow_left₀ (h.nonneg t) h5 n
    _ = a := Real.rpow_inv_natCast_pow ha.1.le (by omega)

/-- Proof of Proposition prop:gauge: "Let f satisfy p(f) > 0 and let p_f(t) = inf p(tfⁿ)/p(f)ⁿ; the sequence is nonincreasing.
It is again such a gauge: p_f(1) = 1, submultiplicativity follows from p(stf^(a+b)) ≤ p(sfᵃ)p(tfᵇ), and the two other
properties pass to the limit." Here p(fⁿ) = p(f)ⁿ is a hypothesis. The statement says of q = p_f what is used: it is a gauge
below p, it keeps what p keeps, and it keeps (1, f, 1/p(f)), that is, p(f)·p_f(t) ≤ p_f(tf). -/
theorem prop_gauge_localize (h : IsPre D p) {f : M} (hf : 0 < p f) (hpow : ∀ n, p (f ^ n) = p f ^ n) :
    ∃ q : M → ℝ, IsPre D q ∧ (∀ t, q t ≤ p t) ∧ Keeps q 1 f (p f)⁻¹ ∧
      ∀ x y c, 0 ≤ c → Keeps p x y c → Keeps q x y c := by
  set P : ℕ → M → ℝ := fun n t => p (t * f ^ n) / p f ^ n with hP
  have anti : Antitone P := by
    refine antitone_nat_of_succ_le fun n t => ?_
    simp only [hP]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc p (t * f ^ (n + 1)) * p f ^ n ≤ (p (t * f ^ n) * p f) * p f ^ n := by
          gcongr
          rw [pow_succ, ← mul_assoc]
          exact h.mul_le _ _
      _ = p (t * f ^ n) * p f ^ (n + 1) := by ring
  have nonneg : ∀ n t, 0 ≤ P n t := fun n t => div_nonneg (h.nonneg _) (by positivity)
  have hle : ∀ n t, ⨅ j, P j t ≤ P n t := fun n t =>
    ciInf_le ⟨0, by rintro _ ⟨i, rfl⟩; exact nonneg i t⟩ n
  refine ⟨fun t => ⨅ n, P n t, isPre_iInf anti.directed_ge nonneg ?_ ?_ ?_, ?_, ?_, ?_⟩
  · intro n
    simp only [hP, one_mul, hpow]
    exact div_self (by positivity)
  · intro n s t
    refine ⟨n + n, ?_⟩
    simp only [hP]
    rw [div_mul_div_comm, ← pow_add]
    gcongr
    have : s * t * f ^ (n + n) = (s * f ^ n) * (t * f ^ n) := by
      rw [pow_add]; exact mul_mul_mul_comm _ _ _ _
    rw [this]
    exact h.mul_le _ _
  · intro n κ _ t b hb
    have h1 := h.le_sum _ _ (D.mul (f ^ n) hb)
    simp only [hP]
    rw [← Finset.sum_div]
    gcongr
  · intro t
    simpa [hP] using hle 0 t
  · intro t
    rw [mul_one, Real.mul_iInf_of_nonneg (by positivity)]
    refine le_ciInf fun n => (hle (n + 1) t).trans (le_of_eq ?_)
    simp only [hP]
    rw [pow_succ' f n, ← mul_assoc, pow_succ]
    field_simp
  · intro x y c hc hk
    refine keeps_iInf nonneg hc fun n t => ?_
    simp only [hP]
    rw [mul_div_assoc']
    gcongr
    have := hk (t * f ^ n)
    rwa [mul_right_comm, mul_right_comm t y]

/-- Proposition prop:gauge for a commutative monoid with a covering relation: below every gauge p₀ there is a gauge that is
multiplicative and keeps every triple which p₀ keeps. -/
theorem prop_gauge_monoid {p₀ : M → ℝ} (h₀ : IsPre D p₀) :
    ∃ F : M → ℝ, IsPre D F ∧ (∀ s t, F (s * t) = F s * F t) ∧ (∀ t, F t ≤ p₀ t) ∧
      ∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps F x y c := by
  obtain ⟨p, hp, hle, hkeep, hmin⟩ := prop_gauge_minimal h₀
  -- "By minimality r = p, that is, p(tⁿ) = p(t)ⁿ."
  have hrad : ∀ t, sInf (rad p t) = p t :=
    hmin _ (prop_gauge_radius hp) (fun x y c hc hk => prop_gauge_radius_keeps hp hc (hkeep x y c hc hk))
      (prop_gauge_radius_le hp)
  refine ⟨p, hp, fun s f => le_antisymm (hp.mul_le s f) ?_, hle, hkeep⟩
  rcases (hp.nonneg f).eq_or_lt with hf | hf
  · -- "If p(f) = 0, then p(tf) = 0 as well."
    rw [← hf, mul_zero]
    exact hp.nonneg _
  · -- "By minimality p_f = p, hence p(tf) = p(t)p(f)."
    obtain ⟨q, hq, hqle, hqk, hqkeep⟩ := prop_gauge_localize hp hf (prop_gauge_radius_pow hp hrad f)
    have hqp := hmin q hq (fun x y c hc hk => hqkeep x y c hc (hkeep x y c hc hk)) hqle
    have h1 := hqk s
    rw [hqp, hqp, mul_one, inv_mul_eq_div, le_div_iff₀ hf] at h1
    exact h1

end Monoid

/-- **Paper: Proposition prop:gauge.** "Below every gauge there is a spectral point that keeps every triple which the
gauge keeps." A gauge is an Ov.PreSpec; it keeps (x, y, c) if p(tx) ≤ c p(ty) for all t. This is prop_gauge_monoid for the
classes of tensors. -/
theorem prop_gauge (p : PreSpec K I) :
    ∃ φ : Spec K I, (∀ t, φ.F t ≤ p.p t) ∧
      ∀ (x y : Ten K I) (c : ℝ), 0 ≤ c → (∀ t, p.p (t * x) ≤ c * p.p (t * y)) →
        ∀ t, φ.F (t * x) ≤ c * φ.F (t * y) := by
  obtain ⟨F, hF, hmul, hle, hk⟩ := prop_gauge_monoid (isPre_onCls p)
  refine ⟨⟨fun t => F (cls t), fun _ => hF.nonneg _, hF.one, fun s t => by rw [cls_mul, hmul],
    fun s b hb => hF.le_sum _ _ (tenCover_cov.2 hb)⟩, fun t => ?_, fun x y c hc h t => ?_⟩
  · exact (hle (cls t)).trans (onCls_cls p t).le
  · have h1 := hk (cls x) (cls y) c hc (keeps_onCls h) (cls t)
    rwa [← cls_mul, ← cls_mul] at h1

section Certificates

variable {M : Type*} [CommMonoid M] {D : Cover M} {B : Type} [Fintype B]

/-- Proof of Theorem thm:duality, first half: "Let p(t) be the infimum of the weights of all certificates for t. Certificates
can be multiplied, and can be raised to a common level and added along covers. As the trivial certificate of level 0 gives
p(1) ≤ 1, and copies of 1 give every t a certificate of level 0, the function p is a gauge if p(1) ≥ 1. … Multiplying a
certificate for tC by A_β gives one for tA_β of one level higher and η times the weight; so p keeps (A_β, C, η)." -/
theorem thm_duality_gauge {C : M} {A : B → M} {η : ℝ} (hη : 0 < η)
    (hone : ∀ t : M, ∃ r : ℕ, D.cov t (fun _ : Fin r => (1 : M)))
    (h : ∀ k W, Cert D C A η 1 k W → 1 ≤ W) :
    IsPre D (fun t => sInf {W | ∃ k, Cert D C A η t k W}) ∧
      ∀ β, Keeps (fun t => sInf {W | ∃ k, Cert D C A η t k W}) (A β) C η := by
  set S : M → Set ℝ := fun t => {W | ∃ k, Cert D C A η t k W} with hS
  have hne : ∀ t, (S t).Nonempty := by
    intro t
    obtain ⟨r, hr⟩ := hone t
    exact ⟨_, 0, Cert.cover hr fun _ => Cert.one 0⟩
  have h0 : ∀ t, ∀ w ∈ S t, 0 ≤ w := fun t w ⟨k, hk⟩ => hk.nonneg hη
  refine ⟨isPre_sInf hne h0 ⟨0, Cert.one 0⟩ (fun w ⟨k, hk⟩ => h k w hk)
    (fun s t a ⟨k, hk⟩ b ⟨l, hl⟩ => ⟨k + l, hk.mul hη hl⟩) ?_, fun β => ?_⟩
  · intro κ _ t b hb w hw
    choose k hk using hw
    exact ⟨_, ⟨∑ j, k j, Cert.cover hb fun j => (hk j).raise hη
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))⟩, le_rfl⟩
  · exact keeps_sInf hne h0 hη fun t w ⟨k, hk⟩ => ⟨k + 1, hk.mul_gen hη β⟩

/-- Proof of Theorem thm:duality: "So p(1) < 1, and 1 has a certificate of some level k and weight below 1. Then k ≥ 1, and
every term has v_j ≠ 0, as it would weigh 1 otherwise: this is a cover of C^k by terms in which at least one C was
exchanged." (The certificate of level k₀ is raised to the level k = k₀ + 1.) -/
theorem thm_duality_exchange {C : M} {A : B → M} {η : ℝ} (hη : 0 < η) {k₀ : ℕ} {W : ℝ}
    (h : Cert D C A η 1 k₀ W) (hW1 : W < 1) :
    ∃ (κ : Type) (_ : Fintype κ) (u : κ → ℕ) (v : κ → B → ℕ), (∀ j, u j + ∑ β, v j β = k₀ + 1) ∧
      (∀ j, u j < k₀ + 1) ∧ D.cov (C ^ (k₀ + 1)) (fun j => C ^ u j * mon A (v j)) ∧
      ∑ j, η ^ (∑ β, v j β) ≤ 1 := by
  obtain ⟨κ, _, u, v, hu, hc, hW⟩ := h.raise hη (Nat.le_succ k₀)
  rw [one_mul] at hc
  have hlt : ∑ j, η ^ (∑ β, v j β) < 1 := hW.trans_lt hW1
  refine ⟨κ, inferInstance, u, v, hu, fun j => ?_, hc, hlt.le⟩
  by_contra hge
  have h1 := hu j
  have h2 : ∑ β, v j β = 0 := by omega
  have h3 := Finset.single_le_sum (f := fun j => η ^ (∑ β, v j β))
    (fun j _ => by positivity) (Finset.mem_univ j)
  simp only [h2, pow_zero] at h3
  linarith

/-- Proof of Theorem thm:duality: "In C^N replace C^k by this cover as long as some term contains it. The total weight never
increases, so it stays at most 1, and each final term has fewer than k factors C." -/
theorem thm_duality_replace {C : M} {A : B → M} {η : ℝ} (hη : 0 < η) {k : ℕ} {κ : Type} [Fintype κ] {u : κ → ℕ}
    {v : κ → B → ℕ} (hu : ∀ j, u j + ∑ β, v j β = k) (huk : ∀ j, u j < k)
    (hc : D.cov (C ^ k) (fun j => C ^ u j * mon A (v j))) (hw : ∑ j, η ^ (∑ β, v j β) ≤ 1) (N : ℕ) :
    ∃ (κ' : Type) (_ : Fintype κ') (u' : κ' → ℕ) (v' : κ' → B → ℕ),
      (∀ j, u' j < k) ∧ (∀ j, u' j + ∑ β, v' j β = N) ∧
      D.cov (C ^ N) (fun j => C ^ u' j * mon A (v' j)) ∧ ∑ j, η ^ (∑ β, v' j β) ≤ 1 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N k with hN | hN
    · exact ⟨Unit, inferInstance, fun _ => N, fun _ _ => 0, fun _ => by simpa using hN,
        by simp, by simpa [mon_zero] using D.refl (C ^ N), by simp⟩
    · have hN' : ∀ j, N - k + u j < N := fun j => by have := huk j; omega
      choose μ i u' v' hu' hs' hc' hw' using fun j => ih _ (hN' j)
      refine ⟨Σ j, μ j, inferInstance, fun x => u' x.1 x.2, fun x β => v x.1 β + v' x.1 x.2 β,
        fun x => hu' _ _, fun x => ?_, ?_, ?_⟩
      · have h1 := hs' x.1 x.2
        have h2 := hu x.1
        rw [Finset.sum_add_distrib]
        dsimp only
        omega
      · have h1 : D.cov (C ^ N) (fun j => C ^ (N - k + u j) * mon A (v j)) := by
          have h2 := D.mul (C ^ (N - k)) hc
          rw [← pow_add, Nat.add_sub_cancel' hN] at h2
          convert h2 using 2 with j
          rw [pow_add]
          ac_rfl
        refine D.bind (c := fun j (x : μ j) =>
          C ^ u' j x * mon A (fun β => v j β + v' j x β)) h1 fun j => ?_
        have h2 := D.mul (mon A (v j)) (hc' j)
        convert h2 using 2 with x
        rw [mon_add]
        ac_rfl
      · rw [Fintype.sum_sigma]
        refine le_trans (Finset.sum_le_sum fun j _ => ?_) hw
        calc ∑ x, η ^ (∑ β, (v j β + v' j x β)) =
            η ^ (∑ β, v j β) * ∑ x, η ^ (∑ β, v' j x β) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun x _ => by rw [← pow_add, Finset.sum_add_distrib]
          _ ≤ η ^ (∑ β, v j β) * 1 := by gcongr; exact hw' j
          _ = _ := mul_one _

omit [Fintype B] in
/-- Proof of Theorem thm:duality: "Replacing each remaining factor C by a fixed number c of copies of a nonzero A_β": if C is
covered by c copies of a, then Cⁿ is covered by cⁿ copies of aⁿ. -/
theorem thm_duality_copies {C a : M} {c : ℕ} (hc : D.cov C (fun _ : Fin c => a)) (n : ℕ) :
    ∃ (μ : Type) (_ : Fintype μ), Fintype.card μ = c ^ n ∧ D.cov (C ^ n) (fun _ : μ => a ^ n) := by
  induction n with
  | zero => exact ⟨Unit, inferInstance, by simp, by simpa using D.refl (1 : M)⟩
  | succ n ih =>
    obtain ⟨μ, _, hμ, hcov⟩ := ih
    refine ⟨Σ _ : μ, Fin c, inferInstance, ?_, ?_⟩
    · rw [Fintype.card_sigma]
      simp [hμ, pow_succ]
    · have := D.mul_mul hcov hc
      simpa only [pow_succ] using this

/-- Proof of Theorem thm:duality, second half: from a certificate for 1 of level k₀ and weight below 1, and a cover of C by c
copies of some A_β, a cover of C^N by products of N factors. "Hence there are at most η^(-N) terms. Replacing each remaining
factor C by a fixed number c of copies of a nonzero A_β gives at most c^k η^(-N)" terms; the Lean bound has c + 1 for c, and
k = k₀ + 1. -/
theorem thm_duality_cover {C : M} {A : B → M} {η : ℝ} (hη : 0 < η) (hη1 : η < 1) {β₀ : B} {c : ℕ}
    (hcA : D.cov C (fun _ : Fin c => A β₀)) {k₀ : ℕ} {W : ℝ} (h : Cert D C A η 1 k₀ W) (hW1 : W < 1) (N : ℕ) :
    ∃ (κ : Type) (_ : Fintype κ) (v : κ → B → ℕ),
      (Fintype.card κ : ℝ) ≤ ((c : ℝ) + 1) ^ (k₀ + 1) * (η⁻¹) ^ N ∧ (∀ j, ∑ β, v j β = N) ∧
      D.cov (C ^ N) (fun j => mon A (v j)) := by
  classical
  obtain ⟨κ, _, u, v, hu, huk, hc, hw⟩ := thm_duality_exchange hη h hW1
  obtain ⟨κ', _, u', v', hu', hs', hc', hw'⟩ := thm_duality_replace hη hu huk hc hw N
  choose μ i hμ hcov using fun j : κ' => thm_duality_copies hcA (u' j)
  set E : ℝ := ((c : ℝ) + 1) ^ (k₀ + 1) with hE
  refine ⟨Σ j, μ j, inferInstance, fun x β => v' x.1 β + if β = β₀ then u' x.1 else 0,
    ?_, fun x => ?_, ?_⟩
  · rw [Fintype.card_sigma]
    push_cast
    have h1 : ∀ j, (Fintype.card (μ j) : ℝ) ≤ E := fun j => by
      rw [hμ j]
      push_cast
      calc (c : ℝ) ^ u' j ≤ ((c : ℝ) + 1) ^ u' j := by gcongr; linarith
        _ ≤ E := pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) c]) (hu' j).le
    have h2 : (Fintype.card κ' : ℝ) * η ^ N ≤ 1 := by
      refine le_trans ?_ hw'
      rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
      refine Finset.sum_le_sum fun j _ => pow_le_pow_of_le_one hη.le hη1.le ?_
      have := hs' j
      omega
    calc ∑ j, (Fintype.card (μ j) : ℝ) ≤ ∑ _j : κ', E := Finset.sum_le_sum fun j _ => h1 j
      _ = Fintype.card κ' * E := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Fintype.card κ' * η ^ N) * (E * (η⁻¹) ^ N) := by
        rw [inv_pow]
        field_simp
      _ ≤ 1 * (E * (η⁻¹) ^ N) := by gcongr
      _ = _ := one_mul _
  · have := hs' x.1
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    omega
  · refine D.bind (b := fun j => C ^ u' j * mon A (v' j))
      (c := fun j (_ : μ j) => mon A (fun β => v' j β + if β = β₀ then u' j else 0)) hc' fun j => ?_
    have h1 := D.mul (mon A (v' j)) (hcov j)
    convert h1 using 2 with x
    rw [mon_add, mon_single]
    exact mul_comm _ _

end Certificates

/-- **Paper: Theorem thm:duality.** "Let C ≠ 0 and A_1, …, A_r be tensors on I, not all A_β zero, and suppose that
every spectral point satisfies φ(C) ≤ max φ(A_β). Then for every ε > 0 and all large N, the power C^N is covered by at
most 2^(εN) products of N factors from A_1, …, A_r." The family is indexed by any finite type B. -/
theorem thm_duality [Nonempty I] {B : Type} [Fintype B] [DecidableEq B] {C : Ten K I} {A : B → Ten K I}
    (hC : ∃ x, C.val x ≠ 0) (hA : ∃ β x, (A β).val x ≠ 0) (h : ∀ φ : Spec K I, ∃ β, φ.F C ≤ φ.F (A β)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ (m : ℕ) (v : Fin m → B → ℕ), (m : ℝ) ≤ 2 ^ (ε * N) ∧
      (∀ i, ∑ β, v i β = N) ∧
      SumRestr (Ten.kpow C N) fun i => Ten.prod fun β => Ten.kpow (A β) (v i β) := by
  -- η = 2^(-ε/2)
  have hη : (0 : ℝ) < 2 ^ (-(ε / 2)) := by positivity
  have hη1 : (2 : ℝ) ^ (-(ε / 2)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hinv : ((2 : ℝ) ^ (-(ε / 2)))⁻¹ = 2 ^ (ε / 2) := by rw [← Real.rpow_neg (by norm_num), neg_neg]
  have hsq : ∀ N : ℕ, ((2 : ℝ) ^ (ε / 2)) ^ N * ((2 : ℝ) ^ (ε / 2)) ^ N = 2 ^ (ε * N) := by
    intro N
    rw [← mul_pow, ← Real.rpow_add (by norm_num), add_halves, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  -- copies of 1, and so of any nonzero tensor, cover every tensor
  have hcov : ∀ (t : Ten K I) {s : Ten K I}, Restr 1 s →
      ∃ r : ℕ, (tenCover K I).cov (cls t) (fun _ : Fin r => cls s) := fun t s hs => by
    obtain ⟨r, hr⟩ := tensor_covered_by_ones t
    exact ⟨r, tenCover_cov.2 (hr.mono fun _ => hs)⟩
  have hone : ∀ t : Cls K I, ∃ r : ℕ, (tenCover K I).cov t (fun _ : Fin r => (1 : Cls K I)) := by
    intro t
    obtain ⟨r, hr⟩ := hcov (rep t) (Restr.refl 1)
    rw [cls_rep] at hr
    exact ⟨r, hr⟩
  obtain ⟨β₀, hβ₀⟩ := hA
  by_cases hcert : ∃ k W, Cert (tenCover K I) (cls C) (fun β => cls (A β)) (2 ^ (-(ε / 2))) 1 k W ∧ W < 1
  · -- 1 has a certificate of weight below 1
    obtain ⟨k, W, hc, hW⟩ := hcert
    obtain ⟨c, hcA⟩ := hcov C (tensor_one_restr hβ₀)
    have hbase : (1 : ℝ) < 2 ^ (ε / 2) := Real.one_lt_rpow one_lt_two (by linarith)
    -- c^k η^(-N) ≤ 2^(εN) for large N
    obtain ⟨N₀, hN₀⟩ := pow_unbounded_of_one_lt (((c : ℝ) + 1) ^ (k + 1)) hbase
    refine ⟨N₀, fun N hN => ?_⟩
    obtain ⟨κ, _, v, hcard, hv, hc⟩ := thm_duality_cover hη hη1 (β₀ := β₀) hcA hc hW N
    let e := Fintype.equivFin κ
    refine ⟨Fintype.card κ, fun i => v (e.symm i), ?_, fun i => hv _, ?_⟩
    · rw [hinv] at hcard
      refine hcard.trans (le_trans ?_ (hsq N).le)
      gcongr
      exact hN₀.le.trans (pow_le_pow_right₀ hbase.le hN)
    simp only [cls_mon, ← cls_kpow] at hc
    exact (tenCover_cov.1 hc).reindex e.symm
  · -- otherwise the weights of certificates are a gauge, and Proposition prop:gauge contradicts the hypothesis
    exfalso
    push Not at hcert
    obtain ⟨hp, hA⟩ := thm_duality_gauge (D := tenCover K I) (C := cls C) (A := fun β => cls (A β)) hη hone hcert
    obtain ⟨φ, -, hk⟩ := prop_gauge (ofCls hp)
    obtain ⟨β, hβ⟩ := h φ
    have h2 := hk (A β) C _ hη.le (fun t => by
      have h5 := hA β (cls t)
      rw [← cls_mul, ← cls_mul] at h5
      exact h5) 1
    rw [(def_spectral_congr φ).2 (Equi.one_mul _), (def_spectral_congr φ).2 (Equi.one_mul _)] at h2
    have h3 : 1 ≤ φ.F C := (def_spectral_values φ C).1 hC
    nlinarith

end Paper
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Tensors, prices and duality": extension

The subsection "Extension": Proposition prop:extend, with the steps of its proof.
-/

namespace Paper

open Ov Ov.Ten Ov.Duality Nc.Price Finset

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

variable {I' : Type} [Fintype I'] [DecidableEq I'] {L : Type} [Fintype L]

/-- The product on the right in Proposition prop:extend: "Call the product on the right f(t)". -/
noncomputable def extendProduct (π : L → I' → I) (θ : L → ℝ) (φ : Spec K I) (t : Ten K I') : ℝ :=
  ∏ l, φ.F (Ten.push (π l) t) ^ θ l

/-- Proof of Proposition prop:extend: "Call the product on the right f(t); it is multiplicative and monotone." Also f ≥ 0 and
f(1) = 1. -/
theorem prop_extend_product (π : L → I' → I) (θ : L → ℝ) (hθ : ∀ l, 0 ≤ θ l) (φ : Spec K I) :
    (∀ t, 0 ≤ extendProduct π θ φ t) ∧ extendProduct π θ φ 1 = 1 ∧
    (∀ s t, extendProduct π θ φ (s * t) = extendProduct π θ φ s * extendProduct π θ φ t) ∧
    ∀ {s t}, Restr s t → extendProduct π θ φ s ≤ extendProduct π θ φ t := by
  refine ⟨fun t => Finset.prod_nonneg fun l _ => Real.rpow_nonneg (φ.nonneg _) _, ?_, fun s t => ?_, fun {s t} h => ?_⟩
  · refine Finset.prod_eq_one fun l _ => ?_
    rw [(def_spectral_congr φ).2 (tensor_push_one _), φ.one, Real.one_rpow]
  · rw [extendProduct, extendProduct, extendProduct, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [(def_spectral_congr φ).2 (tensor_push_mul _ s t), φ.mul, Real.mul_rpow (φ.nonneg _) (φ.nonneg _)]
  · exact Finset.prod_le_prod (fun l _ => Real.rpow_nonneg (φ.nonneg _) _) fun l _ =>
      Real.rpow_le_rpow (φ.nonneg _) ((def_spectral_congr φ).1 ((tensor_push_cover _).2 h)) (hθ l)

/-- Proof of Proposition prop:extend: "Suppose that ιA = ∑ s_j, each s_j a restriction of b_j. As ιA has trivial index sets
outside ι(I), so has every s_j; so s_j = ιa_j with ∑ a_j = A. Push-forwards preserve restrictions, so a_j = π_l s_j is a
restriction of π_l b_j for every l." -/
theorem prop_extend_cover (ι : I → I') {A : Ten K I} {κ : Type} [Fintype κ] {b : κ → Ten K I'}
    (h : Ten.SumRestr (Ten.push ι A) b) :
    ∃ c : κ → Ten K I, Ten.SumRestr A c ∧
      ∀ k, ∀ π : I' → I, (∀ i, π (ι i) = i) → Ten.Restr (c k) (Ten.push π (b k)) := by
  obtain ⟨v, hv, hr⟩ := Ten.sumRestr_iff.1 h
  let emb : (∀ i, A.ι i) → ∀ q, (Ten.push ι A).ι q := fun x q j => x j.1
  refine ⟨fun k => A.withVal fun x => v k (emb x), Ten.SumRestr.of_withVal A _ fun x => ?_,
    fun k π hπ => ?_⟩
  · exact hv (emb x)
  · have h1 : Ten.Restr (Ten.push ι (A.withVal fun x => v k (emb x)))
        ((Ten.push ι A).withVal (v k)) := by
      refine Ten.Restr.of_map' (fun q x => x) fun x => ?_
      rw [Ten.push_val]
      change v k _ = v k _
      congr 1
      funext q j
      obtain ⟨j, rfl⟩ := j
      rfl
    have h2 := (tensor_push_cover π).2 (h1.trans (hr k))
    have h3 : π ∘ ι = id := funext hπ
    have h4 := tensor_push_comp π ι (A.withVal fun x => v k (emb x))
    rw [h3] at h4
    exact (h4.trans (tensor_push_id _)).2.trans h2

/-- Proof of Proposition prop:extend: "So φ(A) ≤ ∑ φ(a_j) ≤ ∑ f(b_j)", for every cover (b_j) of ιA. -/
theorem prop_extend_lower (ι : I → I') (π : L → I' → I) (hπ : ∀ l i, π l (ι i) = i) (θ : L → ℝ) (hθ : ∀ l, 0 ≤ θ l)
    (hθ1 : ∑ l, θ l = 1) (φ : Spec K I) (A : Ten K I) {κ : Type} [Fintype κ] (b : κ → Ten K I')
    (hb : SumRestr (Ten.push ι A) b) : φ.F A ≤ ∑ k, extendProduct π θ φ (b k) := by
  obtain ⟨a, ha, hr⟩ := prop_extend_cover ι hb
  refine (φ.le_sum A a ha).trans (Finset.sum_le_sum fun k _ => ?_)
  -- φ(a_j) is at most every factor φ(π_l b_j), so at most their weighted geometric mean
  rcases (φ.nonneg (a k)).eq_or_lt with h0 | h0
  · rw [← h0]
    exact (prop_extend_product π θ hθ φ).1 _
  · calc φ.F (a k) = φ.F (a k) ^ (∑ l, θ l) := by rw [hθ1, Real.rpow_one]
      _ = ∏ l, φ.F (a k) ^ θ l := Real.rpow_sum_of_pos h0 _ _
      _ ≤ extendProduct π θ φ (b k) := Finset.prod_le_prod (fun l _ => Real.rpow_nonneg h0.le _) fun l _ =>
        Real.rpow_le_rpow h0.le ((def_spectral_congr φ).1 (hr k _ (hπ l))) (hθ l)

/-- Proof of Proposition prop:extend: "f(ιA) = φ(A), as π_l ι = id." -/
theorem prop_extend_upper (ι : I → I') (π : L → I' → I) (hπ : ∀ l i, π l (ι i) = i) (θ : L → ℝ)
    (hθ1 : ∑ l, θ l = 1) (φ : Spec K I) (A : Ten K I) : extendProduct π θ φ (Ten.push ι A) = φ.F A := by
  have retr : ∀ l, Equi (Ten.push (π l) (Ten.push ι A)) A := by
    intro l
    have h := tensor_push_comp (π l) ι A
    rw [show π l ∘ ι = id from funext (hπ l)] at h
    exact h.trans (tensor_push_id _)
  have h1 : extendProduct π θ φ (Ten.push ι A) = ∏ l, φ.F A ^ θ l :=
    Finset.prod_congr rfl fun l _ => by rw [(def_spectral_congr φ).2 (retr l)]
  rw [h1]
  rcases (φ.nonneg A).eq_or_lt with h0 | h0
  · obtain ⟨l, hl⟩ : ∃ l, θ l ≠ 0 := by
      by_contra hne
      push Not at hne
      simp [hne] at hθ1
    rw [← h0]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (Real.zero_rpow hl)
  · rw [← Real.rpow_sum_of_pos h0, hθ1, Real.rpow_one]

/-- Proof of Proposition prop:extend: there is "a gauge with p ≤ f and p(ιA) = φ(A) for all A". In the proof it is the printed
one: "Let p(t) be the infimum of ∑ f(b_j) over the covers (b_j) of t. … With A = 1 this shows p(1) = 1". -/
theorem prop_extend_gauge (ι : I → I') (π : L → I' → I) (hπ : ∀ l i, π l (ι i) = i) (θ : L → ℝ) (hθ : ∀ l, 0 ≤ θ l)
    (hθ1 : ∑ l, θ l = 1) (φ : Spec K I) :
    ∃ p : PreSpec K I', (∀ t, p.p t ≤ extendProduct π θ φ t) ∧ ∀ A : Ten K I, p.p (Ten.push ι A) = φ.F A := by
  classical
  obtain ⟨f0, f1, fmul, fmono⟩ := prop_extend_product π θ hθ φ
  set f : Ten K I' → ℝ := extendProduct π θ φ with hf
  have hcongr : ∀ {s t : Ten K I'}, Equi s t → f s = f t := fun h => le_antisymm (fmono h.1) (fmono h.2)
  -- the sums ∑ f(b_j) over the covers of a class of tensors
  set S : Cls K I' → Set ℝ := fun m => {W | ∃ (κ : Type) (_ : Fintype κ) (b : κ → Cls K I'),
    (tenCover K I').cov m b ∧ ∑ k, f (rep (b k)) = W} with hS
  have hne : ∀ t, (S t).Nonempty := fun t =>
    ⟨_, Unit, inferInstance, fun _ => t, (tenCover K I').refl t, rfl⟩
  have h0 : ∀ t, ∀ w ∈ S t, 0 ≤ w := by
    rintro t w ⟨κ, _, b, -, rfl⟩
    exact Finset.sum_nonneg fun k _ => f0 _
  have hlow : ∀ A : Ten K I, ∀ w ∈ S (cls (Ten.push ι A)), φ.F A ≤ w := by
    rintro A w ⟨κ, _, b, hb, rfl⟩
    exact prop_extend_lower ι π hπ θ hθ hθ1 φ A _ ((rep_cls _).2.trans_sum hb)
  have hup : ∀ t : Ten K I', f t ∈ S (cls t) := fun t =>
    ⟨Unit, inferInstance, fun _ => cls t, (tenCover K I').refl _, by
      simpa using hcongr (rep_cls t)⟩
  have hpre : IsPre (tenCover K I') (fun t => sInf (S t)) := by
    refine isPre_sInf hne h0 ?_ ?_ ?_ ?_
    · have h := hup 1
      rwa [f1, cls_one] at h
    · intro w hw
      rw [← cls_one, ← cls_eq.2 (tensor_push_one ι)] at hw
      have h := hlow 1 w hw
      rwa [φ.one] at h
    · rintro s t a ⟨κ, _, b, hb, rfl⟩ a' ⟨κ', _, b', hb', rfl⟩
      refine ⟨Σ _ : κ, κ', inferInstance, _, (tenCover K I').mul_mul hb hb', ?_⟩
      rw [Fintype.sum_sigma, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
      rw [← fmul]
      exact hcongr (rep_cls _)
    · intro κ _ t b hb w hw
      choose μ i c hc hw using hw
      refine ⟨_, ⟨Σ k, μ k, inferInstance, _, (tenCover K I').bind hb hc, rfl⟩, ?_⟩
      rw [Fintype.sum_sigma]
      exact (Finset.sum_congr rfl fun k _ => hw k).le
  have Pf : ∀ t, (ofCls hpre).p t ≤ f t := fun t => csInf_le ⟨0, fun _ hw => h0 _ _ hw⟩ (hup t)
  exact ⟨ofCls hpre, Pf, fun A => le_antisymm ((Pf _).trans (prop_extend_upper ι π hπ θ hθ1 φ A).le)
    (le_csInf (hne _) (hlow A))⟩

/-- Proof of Proposition prop:extend: "let c = φ(C) and q(t) = inf p(t ιCⁿ)/cⁿ. As p(ιCⁿ) = cⁿ, this is a gauge below p that
keeps (1, ιC, 1/c)." Stated for any gauge p and any tensor f with p(f) > 0 and p(fⁿ) = p(f)ⁿ: some gauge q below p keeps
(1, f, 1/p(f)). It is the one of prop_gauge_localize, for the classes of tensors. -/
theorem prop_extend_localize (p : PreSpec K I) (f : Ten K I) (hf : 0 < p.p f)
    (hpow : ∀ n, p.p (Ten.kpow f n) = p.p f ^ n) :
    ∃ q : PreSpec K I, (∀ t, q.p t ≤ p.p t) ∧ ∀ t, q.p (t * 1) ≤ (p.p f)⁻¹ * q.p (t * f) := by
  obtain ⟨q, hq, hle, hk, -⟩ := prop_gauge_localize (isPre_onCls p) (f := cls f) (by simpa using hf)
    (fun n => by rw [← cls_kpow, onCls_cls, onCls_cls, hpow])
  refine ⟨ofCls hq, fun t => (hle _).trans (onCls_cls p t).le, fun t => ?_⟩
  have := hk (cls t)
  rw [onCls_cls] at this
  change q (cls (t * 1)) ≤ _ * q (cls (t * f))
  rwa [cls_mul, cls_mul]

/-- **Paper: Proposition prop:extend.** "Let ι : I → I′ and π_l : I′ → I, l ≤ L, be maps with π_l ι = id, let θ_l ≥ 0
add up to 1, let φ be a spectral point on I, and let C be a tensor on I. There is a spectral point φ′ on I′ with
φ′(t) ≤ ∏ φ(π_l t)^θ_l for all t, and φ′(ιC) = φ(C)." The maps are indexed by any finite type L. -/
theorem prop_extend (ι : I → I') (π : L → I' → I) (hπ : ∀ l i, π l (ι i) = i) (θ : L → ℝ) (hθ : ∀ l, 0 ≤ θ l)
    (hθ1 : ∑ l, θ l = 1) (φ : Spec K I) (C : Ten K I) :
    ∃ φ' : Spec K I', (∀ t, φ'.F t ≤ ∏ l, φ.F (Ten.push (π l) t) ^ θ l) ∧ φ'.F (Ten.push ι C) = φ.F C := by
  obtain ⟨p, pf, pA⟩ := prop_extend_gauge ι π hπ θ hθ hθ1 φ
  rcases (φ.nonneg C).eq_or_lt with hC | hC
  · -- φ(C) = 0 (the printed case C = 0)
    obtain ⟨φ', hφ', -⟩ := prop_gauge p
    exact ⟨φ', fun t => (hφ' t).trans (pf t),
      le_antisymm ((hφ' _).trans (pA C).le) (by rw [← hC]; exact φ'.nonneg _)⟩
  · obtain ⟨q, hq, hqk⟩ := prop_extend_localize p (Ten.push ι C) (by rwa [pA]) (fun n => by
      rw [← p.congr (Equi.push_kpow ι C n), pA, pA, φ.kpow])
    -- "A spectral point φ′ ≤ q that keeps this triple has c ≤ φ′(ιC) ≤ f(ιC) = c."
    obtain ⟨φ', hφ', hk⟩ := prop_gauge q
    refine ⟨φ', fun t => (hφ' t).trans ((hq t).trans (pf t)),
      le_antisymm ((hφ' _).trans ((hq _).trans (pA C).le)) ?_⟩
    have h1 := hk 1 (Ten.push ι C) _ (by rw [pA]; positivity) hqk 1
    rw [(def_spectral_congr φ').2 (Equi.one_mul _), (def_spectral_congr φ').2 (Equi.one_mul _), φ'.one, pA,
      inv_mul_eq_div, le_div_iff₀ hC, one_mul] at h1
    exact h1

end Paper
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The values of a spectral point at wires

The parts of Lemma lem:exponents (`Paper/Tensors.lean`) in the form in which the development cites them, and what follows
at once for tensors whose legs are moved.
-/

set_option linter.unusedSectionVars false

namespace Ov

open Finset

namespace Spec

open Ten

variable {K : Type} [Field K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (F : Spec K I)

/-- φ(⟨n⟩_P) = n^g with g = log₂ φ(⟨2⟩_P), wherever the legs are. -/
theorem unit_eq [Nonempty I] (π : J → I) {n : ℕ} (hn : 1 ≤ n) :
    F.F (Ten.push π (unit K J n)) = (n : ℝ) ^ Real.logb 2 (F.F (Ten.push π (unit K J 2))) :=
  (Paper.lem_exponents_power F π).2 n hn

/-- φ(⟨n⟩_pq) = n^(d_φ(p,q)). -/
theorem wire_eq (p q : I) {n : ℕ} (hn : 1 ≤ n) : F.F (wire K n p q) = (n : ℝ) ^ F.e p q :=
  Paper.lem_exponents_wire F p q hn

/-- φ(⟨2⟩_pq) = 2^(d_φ(p,q)). -/
theorem wire_two (p q : I) : F.F (wire K 2 p q) = 2 ^ F.e p q := Paper.lem_exponents_wire_two F p q

/-- φ(⟨n⟩_pq) ≤ n^(d_φ(p,q)), also for n = 0. -/
theorem wire_le (p q : I) (n : ℕ) : F.F (wire K n p q) ≤ (n : ℝ) ^ F.e p q := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : F.F (wire K 0 p q) ≤ (0 : ℕ) := F.unit_le ![p, q] 0
    exact this.trans (by exact_mod_cast Real.rpow_nonneg le_rfl _)
  · exact (F.wire_eq p q hn).le

/-- Distances are not negative. -/
theorem e_nonneg (p q : I) : 0 ≤ F.e p q := (Paper.lem_exponents_unit_interval F p q).1

/-- Distances are at most 1. -/
theorem e_le_one (p q : I) : F.e p q ≤ 1 := (Paper.lem_exponents_unit_interval F p q).2

/-- The distance from a party to itself is 0. -/
theorem e_self (p : I) : F.e p p = 0 := Paper.lem_exponents_self F p

/-- Distances are symmetric. -/
theorem e_comm (p q : I) : F.e p q = F.e q p := Paper.lem_exponents_symm F p q

/-- A tensor with all its legs at one party costs at most 1. -/
theorem push_const_le (q : I) (t : Ten K J) : F.F (Ten.push (fun _ => q) t) ≤ 1 := by
  rw [← F.one]
  exact F.mono (Restr.push_const q t)

/-- Moving legs: if the leg j moves from π' j to π j, the value grows at most by the values of wires
between π j and π' j that have the dimensions of the legs. -/
theorem push_le_move (π π' : J → I) (t : Ten K J) :
    F.F (Ten.push π t) ≤
      (∏ j, (Fintype.card (t.ι j) : ℝ) ^ F.e (π j) (π' j)) * F.F (Ten.push π' t) := by
  refine (F.le_mul (Restr.move π π' t)).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (F.nonneg _)
  rw [F.prod]
  exact Finset.prod_le_prod (fun _ _ => F.nonneg _) fun j _ => F.wire_le _ _ _

/-- The distances of a pull-back. -/
theorem pull_e (π : J → I) (p q : J) : (F.pull π).e p q = F.e (π p) (π q) := by
  rw [e, e, pull_F]
  congr 1
  refine F.congr ((Equi.push_push π ![p, q] (unit K (Fin 2) 2)).trans ?_)
  have : π ∘ ![p, q] = ![π p, π q] := by funext i; fin_cases i <;> rfl
  rw [this]
  exact Equi.refl _

end Spec

end Ov
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Prices of wires: the definition

For a field K and a finite set V of parties, `Prices K V` is the closure (for pointwise limits) of the
multiples c·d_F, c ≥ 0, of the metrics d_F(u,v) = F.e u v of the spectral points F over V. A function w
on pairs of any set Y is a price (`IsPrice K w`) if its pull-backs to finite sets are in `Prices`.
That prices are pseudometrics, closed under pull-backs, multiples and limits, and compact below a bound is
in `Paper/Prices.lean`. At the end there are two lemmas on the entries of a wire, for the files that compute with them.
-/

namespace Nc.Price

open Ov Finset

section Finite

variable (K : Type) [Field K]

variable {K} {U V : Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

theorem specCone_comp (f : U → V) {d : V → V → ℝ} (h : d ∈ specCone K V) :
    (fun a b => d (f a) (f b)) ∈ specCone K U := by
  obtain ⟨F, c, hc, rfl⟩ := h
  exact ⟨F.pull f, c, hc, by funext a b; rw [F.pull_e]⟩

theorem continuous_comp {X Y : Type*} (f : X → Y) :
    Continuous fun (d : Y → Y → ℝ) (a b : X) => d (f a) (f b) := by
  fun_prop

theorem prices_comp (f : U → V) {d : V → V → ℝ} (h : d ∈ Prices K V) :
    (fun a b => d (f a) (f b)) ∈ Prices K U :=
  map_mem_closure (continuous_comp f) h fun _ hd => specCone_comp f hd

theorem specCone_smul {d : V → V → ℝ} (h : d ∈ specCone K V) {c : ℝ} (hc : 0 ≤ c) :
    (fun a b => c * d a b) ∈ specCone K V := by
  obtain ⟨F, c', hc', rfl⟩ := h
  exact ⟨F, c * c', mul_nonneg hc hc', by funext a b; ring⟩

theorem prices_smul {d : V → V → ℝ} (h : d ∈ Prices K V) {c : ℝ} (hc : 0 ≤ c) :
    (fun a b => c * d a b) ∈ Prices K V :=
  map_mem_closure (f := fun (d : V → V → ℝ) a b => c * d a b) (by fun_prop) h
    fun _ hd => specCone_smul hd hc

/-- A closed property of the metrics of spectral points that is kept by multiples holds for
prices. -/
theorem prices_induction {d : V → V → ℝ} (h : d ∈ Prices K V) {S : Set (V → V → ℝ)}
    (hS : IsClosed S) (hF : ∀ (F : Spec K V) (c : ℝ), 0 ≤ c → (fun u v => c * F.e u v) ∈ S) :
    d ∈ S := by
  refine closure_minimal ?_ hS h
  rintro _ ⟨F, c, hc, rfl⟩
  exact hF F c hc

end Finite

section General

variable (K : Type) [Field K]

variable {K}

theorem IsPrice.mem {Y : Type*} {w : Y → Y → ℝ} (h : IsPrice K w) {V : Type} [Fintype V]
    [DecidableEq V] (g : V → Y) : (fun a b => w (g a) (g b)) ∈ Prices K V := by
  have h1 := prices_comp (Fintype.equivFin V) (h _ fun i => g ((Fintype.equivFin V).symm i))
  simpa using h1

theorem isPrice_of_mem {V : Type} [Fintype V] [DecidableEq V] {d : V → V → ℝ}
    (h : d ∈ Prices K V) : IsPrice K d := fun _ f => prices_comp f h

/-- The metric of a spectral point is a price. -/
theorem isPrice_spec {V : Type} [Fintype V] [DecidableEq V] (F : Spec K V) :
    IsPrice K F.e :=
  isPrice_of_mem (subset_closure ⟨F, 1, zero_le_one, by simp⟩)

/-- A function is a price if its restrictions to finite subsets are. -/
theorem isPrice_of_finset {Y : Type*} {w : Y → Y → ℝ}
    (h : ∀ S : Finset Y, IsPrice K fun a b : S => w a b) : IsPrice K w := by
  classical
  intro n f
  exact h (Finset.univ.image f) n fun i => ⟨f i, by simp⟩

variable {Y : Type*} {w : Y → Y → ℝ}

/-- Approximation by the metric of a spectral point. -/
theorem IsPrice.exists_spec (h : IsPrice K w) {V : Type} [Fintype V] [DecidableEq V] (g : V → Y)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (F : Spec K V) (c : ℝ), 0 ≤ c ∧ ∀ a b, |w (g a) (g b) - c * F.e a b| < δ := by
  obtain ⟨d, ⟨F, c, hc, rfl⟩, hd⟩ := Metric.mem_closure_iff.1 (h.mem g) δ hδ
  refine ⟨F, c, hc, fun a b => ?_⟩
  have := (dist_pi_lt_iff hδ).1 ((dist_pi_lt_iff hδ).1 hd a) b
  rwa [Real.dist_eq] at this

/-- 0 is a price. -/
theorem isPrice_zero : IsPrice K fun _ _ : Y => 0 := fun n _ =>
  subset_closure ⟨Paper.trivialPoint K (Fin n), 0, le_rfl, by simp⟩

end General

section Unit

open Ov.Ten

variable {K : Type} [Field K]

/-- The entries of the unit tensor with two legs (a wire before it is placed). -/
theorem unit_two_val {n : ℕ} (y : Fin 2 → Fin n) :
    (unit K (Fin 2) n).val y = if y 0 = y 1 then 1 else 0 := by
  rw [unit_val]
  simp [Fin.forall_fin_two, eq_comm]

theorem unit_two_val' {n : ℕ} {β : Type} [DecidableEq β] (ε : Fin n ≃ β) (y : Fin 2 → Fin n) :
    (unit K (Fin 2) n).val y = if ε (y 0) = ε (y 1) then 1 else 0 := by
  rw [unit_two_val]
  simp only [ε.injective.eq_iff]

end Unit

end Nc.Price
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Tensors, prices and duality": prices

The subsection "Prices". The definitions are in Nc/Price/Basic.lean.
-/

namespace Paper

open Ov Ov.Ten Nc.Price Finset Filter MeasureTheory

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- **Paper: Definition def:price.** "A price on a finite set V is a limit of multiples s·d_φ, s ≥ 0, φ a spectral
point on V. A function on the pairs of an arbitrary set Y is a price if all its pull-backs to finite sets are prices." -/
theorem def_price :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (d : V → V → ℝ), IsPrice K d ↔
      ∀ δ : ℝ, 0 < δ → ∃ (φ : Spec K V) (s : ℝ), 0 ≤ s ∧ ∀ u v, |d u v - s * φ.e u v| < δ) ∧
    ∀ (Y : Type) (w : Y → Y → ℝ), IsPrice K w ↔
      ∀ (V : Type) [Fintype V] [DecidableEq V] (g : V → Y), IsPrice K fun u v => w (g u) (g v) := by
  refine ⟨fun V _ _ d => ⟨fun h δ hδ => h.exists_spec id hδ, fun h => isPrice_of_mem ?_⟩,
    fun Y w => ⟨fun h V _ _ g n f => h n fun i => g (f i), fun h n f => (h (Fin n) f).mem id⟩⟩
  rw [Prices, Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨φ, s, hs, hd⟩ := h δ hδ
  refine ⟨_, ⟨φ, s, hs, rfl⟩, (dist_pi_lt_iff hδ).2 fun u => (dist_pi_lt_iff hδ).2 fun v => ?_⟩
  rw [Real.dist_eq]
  exact hd u v

section Facts

variable {Y : Type*} {w : Y → Y → ℝ}

/-- "Prices are pseudometrics." By Lemma lem:exponents the d_φ are; the conditions are closed and kept by multiples. -/
theorem def_price_pseudometric (h : IsPrice K w) :
    (∀ a b, 0 ≤ w a b) ∧ (∀ a, w a a = 0) ∧ (∀ a b, w a b = w b a) ∧ ∀ a b c, w a c ≤ w a b + w b c := by
  refine ⟨fun a b => ?_, fun a => ?_, fun a b => ?_, fun a b c => ?_⟩
  · have h2 : (fun i j : Fin 2 => w (![a, b] i) (![a, b] j)) ∈ {d : Fin 2 → Fin 2 → ℝ | 0 ≤ d 0 1} :=
      prices_induction (h 2 ![a, b]) (isClosed_le continuous_const (by fun_prop)) fun φ c hc => by
        obtain ⟨-, -, -, -, -, -, hI, -⟩ := lem_exponents φ
        exact mul_nonneg hc (hI 0 1).1
    exact h2
  · have h2 : (fun i j : Fin 1 => w (![a] i) (![a] j)) ∈ {d : Fin 1 → Fin 1 → ℝ | d 0 0 = 0} :=
      prices_induction (h 1 ![a]) (isClosed_eq (by fun_prop) continuous_const) fun φ c hc => by
        obtain ⟨-, -, -, h0, -⟩ := lem_exponents φ
        show c * φ.e 0 0 = 0
        rw [h0, mul_zero]
    exact h2
  · have h2 : (fun i j : Fin 2 => w (![a, b] i) (![a, b] j)) ∈ {d : Fin 2 → Fin 2 → ℝ | d 0 1 = d 1 0} :=
      prices_induction (h 2 ![a, b]) (isClosed_eq (by fun_prop) (by fun_prop)) fun φ c hc => by
        obtain ⟨-, -, -, -, hs, -⟩ := lem_exponents φ
        show c * φ.e 0 1 = c * φ.e 1 0
        rw [hs]
    exact h2
  · have h2 : (fun i j : Fin 3 => w (![a, b, c] i) (![a, b, c] j)) ∈
        {d : Fin 3 → Fin 3 → ℝ | d 0 2 ≤ d 0 1 + d 1 2} :=
      prices_induction (h 3 ![a, b, c]) (isClosed_le (by fun_prop) (by fun_prop)) fun φ c hc => by
        obtain ⟨-, -, -, -, -, ht, -⟩ := lem_exponents φ
        show c * φ.e 0 2 ≤ c * φ.e 0 1 + c * φ.e 1 2
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (ht _ _ _) hc
    exact h2

/-- "Pull-backs … of prices are prices; for g : V → W one uses t ↦ φ(gt)." (The latter is Nc.Price.specCone_comp, which
makes the two parts of Definition def:price consistent.) -/
theorem def_price_pullback {Z : Type*} (h : IsPrice K w) (g : Z → Y) : IsPrice K fun a b => w (g a) (g b) :=
  fun n f => h n fun i => g (f i)

/-- "Nonnegative multiples … of prices are prices". -/
theorem def_price_multiple (h : IsPrice K w) {c : ℝ} (hc : 0 ≤ c) : IsPrice K fun a b => c * w a b :=
  fun n f => prices_smul (h n f) hc

/-- The set of prices is closed under pointwise convergence. -/
theorem def_price_closed : IsClosed {w : Y → Y → ℝ | IsPrice K w} := by
  have : {w : Y → Y → ℝ | IsPrice K w} = ⋂ (n : ℕ) (f : Fin n → Y),
      (fun (w : Y → Y → ℝ) i j => w (f i) (f j)) ⁻¹' Prices K (Fin n) := by
    ext w
    simp [IsPrice]
  rw [this]
  exact isClosed_iInter fun n => isClosed_iInter fun f =>
    isClosed_closure.preimage (continuous_comp f)

/-- "Pointwise limits of prices are prices". -/
theorem def_price_limit {ι : Type*} {l : Filter ι} [l.NeBot] {d : ι → Y → Y → ℝ}
    (h : ∀ a b, Tendsto (fun i => d i a b) l (nhds (w a b))) (hd : ∀ᶠ i in l, IsPrice K (d i)) : IsPrice K w := by
  refine def_price_closed.mem_of_tendsto ?_ hd
  rw [tendsto_pi_nhds]
  intro a
  rw [tendsto_pi_nhds]
  exact h a

/-- "The prices below a given function form a compact set, by Tychonoff's theorem." -/
theorem def_price_compact (C : Y → Y → ℝ) : IsCompact {w : Y → Y → ℝ | IsPrice K w ∧ ∀ a b, w a b ≤ C a b} := by
  have h1 : IsCompact {w : Y → Y → ℝ | ∀ a, w a ∈ {v : Y → ℝ | ∀ b, v b ∈ Set.Icc 0 (C a b)}} :=
    isCompact_pi_infinite fun a => isCompact_pi_infinite fun b => isCompact_Icc
  have h2 : IsClosed {w : Y → Y → ℝ | ∀ a b, w a b ≤ C a b} := by
    have : {w : Y → Y → ℝ | ∀ a b, w a b ≤ C a b} = ⋂ (a : Y) (b : Y), {w | w a b ≤ C a b} := by
      ext w; simp
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le (by fun_prop) continuous_const
  refine h1.of_isClosed_subset (def_price_closed.inter h2) ?_
  rintro w ⟨hw, hC⟩ a b
  exact ⟨(def_price_pseudometric hw).1 a b, hC a b⟩

end Facts

end Paper

/-! The same facts in the form in which the development cites them. -/

namespace Nc.Price

variable {K : Type} [Field K] {Y : Type*} {w : Y → Y → ℝ}

theorem IsPrice.nonneg (h : IsPrice K w) (a b : Y) : 0 ≤ w a b := (Paper.def_price_pseudometric h).1 a b

theorem IsPrice.self (h : IsPrice K w) (a : Y) : w a a = 0 := (Paper.def_price_pseudometric h).2.1 a

theorem IsPrice.symm (h : IsPrice K w) (a b : Y) : w a b = w b a := (Paper.def_price_pseudometric h).2.2.1 a b

theorem IsPrice.triangle (h : IsPrice K w) (a b c : Y) : w a c ≤ w a b + w b c :=
  (Paper.def_price_pseudometric h).2.2.2 a b c

theorem IsPrice.comp {Z : Type*} (h : IsPrice K w) (g : Z → Y) : IsPrice K fun a b => w (g a) (g b) :=
  Paper.def_price_pullback h g

theorem IsPrice.smul (h : IsPrice K w) {c : ℝ} (hc : 0 ≤ c) : IsPrice K fun a b => c * w a b :=
  Paper.def_price_multiple h hc

theorem isPrice_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {d : ι → Y → Y → ℝ}
    (h : ∀ a b, Filter.Tendsto (fun i => d i a b) l (nhds (w a b))) (hd : ∀ᶠ i in l, IsPrice K (d i)) : IsPrice K w :=
  Paper.def_price_limit h hd

theorem isCompact_isPrice_le (C : Y → Y → ℝ) : IsCompact {w : Y → Y → ℝ | IsPrice K w ∧ ∀ a b, w a b ≤ C a b} :=
  Paper.def_price_compact C

end Nc.Price

namespace Paper

open Ov Ov.Ten Nc.Price Finset Filter MeasureTheory

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

section Spectral

variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

/-- Proof of Proposition prop:random, the finite case for w = d_φ: "Let C be the product of all wires ⟨2⟩_uv with u, v ∈ Y, and
apply Proposition prop:extend. For every pair e of Y ∪ Q we obtain d_φ′(e) ≤ ∑ θ_l d_φ(π_l e). On Y we have d_φ′ ≤ d_φ with
equality for the sum over all pairs, hence equality for each." -/
theorem prop_random_spectral (F : Spec K P) {m : ℕ} (θ : Fin m → ℝ) (hθ : ∀ l, 0 ≤ θ l)
    (hθ1 : ∑ l, θ l = 1) (σ : Fin m → Q → P) :
    ∃ F' : Spec K (P ⊕ Q), (∀ p p', F'.e (Sum.inl p) (Sum.inl p') = F.e p p') ∧
      ∀ a b, F'.e a b ≤ ∑ l, θ l * F.e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
  classical
  obtain ⟨F', hle, hC⟩ := prop_extend (K := K) (Sum.inl : P → P ⊕ Q)
    (fun l => Sum.elim id (σ l)) (fun l i => rfl) θ hθ hθ1 F
    (Ten.prod fun e : P × P => Ten.wire K 2 e.1 e.2)
  have hb : ∀ a b, F'.e a b ≤ ∑ l, θ l * F.e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
    intro a b
    have h1 := hle (Ten.wire K 2 a b)
    have h2 : ∀ l, F.F (Ten.push (Sum.elim id (σ l)) (Ten.wire K 2 a b)) =
        2 ^ F.e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
      intro l
      rw [← F.pull_F, (F.pull _).wire_two, F.pull_e]
    simp only [h2] at h1
    rw [F'.wire_two] at h1
    have h3 : ∏ l, ((2 : ℝ) ^ F.e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b)) ^ θ l =
        2 ^ ∑ l, θ l * F.e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
      rw [Real.rpow_sum_of_pos (by norm_num)]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [← Real.rpow_mul (by norm_num), mul_comm]
    rw [h3] at h1
    exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h1
  refine ⟨F', ?_, hb⟩
  have hle' : ∀ p p', F'.e (Sum.inl p) (Sum.inl p') ≤ F.e p p' := by
    intro p p'
    refine (hb (Sum.inl p) (Sum.inl p')).trans (le_of_eq ?_)
    simp only [Sum.elim_inl, id]
    rw [← Finset.sum_mul, hθ1, one_mul]
  have hsum : ∑ e : P × P, F'.e (Sum.inl e.1) (Sum.inl e.2) = ∑ e : P × P, F.e e.1 e.2 := by
    rw [← F'.pull_F, (F'.pull _).prod, F.prod] at hC
    simp only [Spec.wire_two, Spec.pull_e] at hC
    rw [← Real.rpow_sum_of_pos (by norm_num), ← Real.rpow_sum_of_pos (by norm_num)] at hC
    have h2 := congrArg (Real.logb 2) hC
    rwa [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_rpow (by norm_num) (by norm_num)]
      at h2
  intro p p'
  have h1 := (Finset.sum_eq_sum_iff_of_le
    (fun (e : P × P) _ => hle' e.1 e.2)).1 hsum (p, p') (Finset.mem_univ _)
  exact h1

end Spectral

section Random

/-- Proof of Proposition prop:random, the reduction to finite sets: "It is enough to find, for all finite Y₀ ⊆ Y and Q₀ ⊆ Q
such that σ maps Q₀ into Y₀, a price on Y₀ ∪ Q₀ with the two properties: these prices form compact sets, so then there is
one that works for all of them at once." Here Z is Y ∪ Q, the two properties are bounds A ≤ |oo′| ≤ B, and the compact
sets are those of def_price_compact. -/
theorem prop_random_compact {Z : Type*} (A B : Z → Z → ℝ)
    (h : ∀ S : Finset Z, ∃ d : S → S → ℝ, IsPrice K d ∧ ∀ a b : S, A a b ≤ d a b ∧ d a b ≤ B a b) :
    ∃ w' : Z → Z → ℝ, IsPrice K w' ∧ ∀ a b, A a b ≤ w' a b ∧ w' a b ≤ B a b := by
  classical
  choose d hd hAB using h
  -- the price on T, as a function on all pairs
  let D : Finset Z → Z → Z → ℝ := fun T a b => if h : a ∈ T ∧ b ∈ T then d T ⟨a, h.1⟩ ⟨b, h.2⟩ else 0
  have hD : ∀ {S T : Finset Z} (hT : S ⊆ T) (a b : S), D T a b = d T ⟨a, hT a.2⟩ ⟨b, hT b.2⟩ :=
    fun hT a b => dif_pos ⟨hT a.2, hT b.2⟩
  let U : Ultrafilter (Finset Z) := Ultrafilter.of atTop
  have hmem : ∀ S : Finset Z, ∀ᶠ T in (U : Filter (Finset Z)), S ⊆ T := fun S =>
    Ultrafilter.of_le _ (eventually_ge_atTop S)
  -- on every finite set S the restrictions have a limit, in the compact set of the prices on S below B
  have key : ∀ S : Finset Z, ∃ v : S → S → ℝ, (IsPrice K v ∧ ∀ a b : S, v a b ≤ B a b) ∧
      ∀ a b : S, Tendsto (fun T => D T a b) U (nhds (v a b)) := by
    intro S
    obtain ⟨v, hv, hlim⟩ := (def_price_compact (K := K) fun a b : S => B a b).ultrafilter_le_nhds
      (U.map fun T (a b : S) => D T a b) (by
        rw [le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
        filter_upwards [hmem S] with T hT
        have e : (fun a b : S => D T a b) = fun a b : S => d T ⟨a, hT a.2⟩ ⟨b, hT b.2⟩ := by
          funext a b
          exact hD hT a b
        refine ⟨?_, fun a b => (hD hT a b).le.trans (hAB T _ _).2⟩
        show IsPrice K fun a b : S => D T a b
        rw [e]
        exact def_price_pullback (hd T) fun a : S => (⟨a, hT a.2⟩ : T))
    have h1 : Tendsto (fun T (a b : S) => D T a b) U (nhds v) := hlim
    exact ⟨v, hv, fun a b => tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h1 a) b⟩
  choose v hv hlim using key
  have ha : ∀ a b : Z, a ∈ ({a, b} : Finset Z) := fun a b => by simp
  have hb : ∀ a b : Z, b ∈ ({a, b} : Finset Z) := fun a b => by simp
  -- the limits fit together
  have hfit : ∀ (S : Finset Z) (a b : S), v S a b = v {a.1, b.1} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩ := fun S a b =>
    tendsto_nhds_unique (hlim S a b) (hlim {a.1, b.1} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩)
  refine ⟨fun a b => v {a, b} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩, isPrice_of_finset fun S => ?_, fun a b => ⟨?_, ?_⟩⟩
  · have e : (fun a b : S => v {a.1, b.1} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩) = v S := by
      funext a b
      exact (hfit S a b).symm
    rw [e]
    exact (hv S).1
  · refine ge_of_tendsto (hlim {a, b} ⟨a, ha _ _⟩ ⟨b, hb _ _⟩) ?_
    filter_upwards [hmem {a, b}] with T hT
    exact ((hAB T _ _).1.trans (hD hT ⟨a, ha _ _⟩ ⟨b, hb _ _⟩).ge :)
  · exact (hv {a, b}).2 ⟨a, ha _ _⟩ ⟨b, hb _ _⟩

/-- Proof of Proposition prop:random, the finite case: "So let Y and Q be finite, and let σ take the values π_l with
probabilities θ_l. By a limit we may assume w = s·d_φ, and then s = 1 by homogeneity." The prices that
prop_random_spectral gives for approximations s·d_φ of w have a limit, since they lie in a compact set (def_price_compact). -/
theorem prop_random_limit {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] {w : P → P → ℝ}
    (hw : IsPrice K w) {m : ℕ} (θ : Fin m → ℝ) (hθ : ∀ l, 0 ≤ θ l) (hθ1 : ∑ l, θ l = 1) (σ : Fin m → Q → P) :
    ∃ w' : P ⊕ Q → P ⊕ Q → ℝ, IsPrice K w' ∧ (∀ p p', w' (Sum.inl p) (Sum.inl p') = w p p') ∧
      ∀ a b, w' a b ≤ ∑ l, θ l * w (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  have hle1 : ∀ n : ℕ, (1 : ℝ) / (n + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  -- w is s·d_φ up to 1/(n+1)
  choose φ s hs hφ using fun n : ℕ => hw.exists_spec (id : P → P) (hpos n)
  choose φ' h1 h2 using fun n => prop_random_spectral (φ n) θ hθ hθ1 σ
  let B : P ⊕ Q → P ⊕ Q → ℝ := fun a b => ∑ l, θ l * w (Sum.elim id (σ l) a) (Sum.elim id (σ l) b)
  let d : ℕ → P ⊕ Q → P ⊕ Q → ℝ := fun n a b => s n * (φ' n).e a b
  have hd : ∀ n, IsPrice K (d n) := fun n => def_price_multiple (isPrice_spec (φ' n)) (hs n)
  have hdB : ∀ n a b, d n a b ≤ B a b + 1 / (n + 1) := by
    intro n a b
    calc s n * (φ' n).e a b
        ≤ s n * ∑ l, θ l * (φ n).e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) :=
          mul_le_mul_of_nonneg_left (h2 n a b) (hs n)
      _ = ∑ l, θ l * (s n * (φ n).e (Sum.elim id (σ l) a) (Sum.elim id (σ l) b)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      _ ≤ ∑ l, θ l * (w (Sum.elim id (σ l) a) (Sum.elim id (σ l) b) + 1 / (n + 1)) := by
        refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (hθ l)
        have h3 := (abs_lt.1 (hφ n (Sum.elim id (σ l) a) (Sum.elim id (σ l) b))).1
        simp only [id] at h3
        linarith
      _ = B a b + 1 / (n + 1) := by
        simp only [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hθ1, one_mul]
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨w', ⟨hw', -⟩, hlim⟩ := (def_price_compact (K := K) fun a b => B a b + 1).ultrafilter_le_nhds (U.map d) (by
    rw [le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
    exact univ_mem' fun n => ⟨hd n, fun a b => (hdB n a b).trans (by linarith [hle1 n])⟩)
  have hlim' : ∀ a b, Tendsto (fun n => d n a b) U (nhds (w' a b)) := by
    intro a b
    have h3 : Tendsto d U (nhds w') := hlim
    exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h3 a) b
  have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) U (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left (Ultrafilter.of_le _)
  refine ⟨w', hw', fun p p' => ?_, fun a b => ?_⟩
  · have h3 : Tendsto (fun n => d n (Sum.inl p) (Sum.inl p') - w p p') U (nhds 0) := by
      refine squeeze_zero_norm (fun n => ?_) hzero
      have h4 := hφ n p p'
      simp only [id] at h4
      rw [Real.norm_eq_abs, abs_sub_comm]
      show |w p p' - s n * (φ' n).e (Sum.inl p) (Sum.inl p')| ≤ _
      rw [h1]
      exact h4.le
    have h4 := tendsto_nhds_unique h3 ((hlim' (Sum.inl p) (Sum.inl p')).sub_const (w p p'))
    linarith
  · exact le_of_tendsto_of_tendsto (hlim' a b) ((hzero.const_add (B a b)).trans (by rw [add_zero]))
      (Eventually.of_forall fun n => hdB n a b)

/-- Proof of Proposition prop:random: "let σ take the values π_l with probabilities θ_l". On a finite set T of new points a
random map, each σ(o) having finitely many values, takes finitely many values π_l; with their probabilities θ_l, the
expectation of any function of the map is a finite mean. -/
theorem prop_random_values {Y Q Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Q → Ω → Y)
    (hfin : ∀ κ, (Set.range (σ κ)).Finite) (hmeas : ∀ κ y, MeasurableSet (σ κ ⁻¹' {y})) (T : Finset Q) :
    ∃ (m : ℕ) (θ : Fin m → ℝ) (π : Fin m → T → Y), (∀ l, 0 ≤ θ l) ∧ ∑ l, θ l = 1 ∧
      ∀ f : (T → Y) → ℝ, ∫ ω, f (fun κ : T => σ κ ω) ∂μ = ∑ l, θ l * f (π l) := by
  classical
  have hfin' : (Set.range fun ω (κ : T) => σ κ ω).Finite := by
    refine (Set.Finite.pi' fun κ : T => hfin κ).subset ?_
    rintro _ ⟨ω, rfl⟩ κ
    exact ⟨ω, rfl⟩
  let V : Finset (T → Y) := hfin'.toFinset
  have hV : ∀ ω, (fun κ : T => σ κ ω) ∈ V := fun ω => by simp [V]
  have hmeas' : ∀ f : T → Y, MeasurableSet {ω | (fun κ : T => σ κ ω) = f} := by
    intro f
    have : {ω | (fun κ : T => σ κ ω) = f} = ⋂ κ : T, σ κ ⁻¹' {f κ} := by
      ext ω
      simp [funext_iff]
    rw [this]
    exact MeasurableSet.iInter fun κ => hmeas _ _
  let e : Fin V.card ≃ V := V.equivFin.symm
  have hmean : ∀ f : (T → Y) → ℝ, ∫ ω, f (fun κ : T => σ κ ω) ∂μ =
      ∑ l : Fin V.card, μ.real {ω | (fun κ : T => σ κ ω) = (e l : T → Y)} * f (e l) := by
    intro f
    have h1 : ∀ ω, f (fun κ : T => σ κ ω) = ∑ g ∈ V,
        ({ω | (fun κ : T => σ κ ω) = g}).indicator (fun _ => f g) ω := by
      intro ω
      rw [Finset.sum_eq_single (fun κ : T => σ κ ω)]
      · rw [Set.indicator_of_mem]; rfl
      · intro g _ hg
        rw [Set.indicator_of_notMem]
        exact fun h => hg h.symm
      · intro h
        exact absurd (hV ω) h
    simp only [h1]
    rw [integral_finsetSum]
    · rw [← Finset.sum_coe_sort V]
      refine (Fintype.sum_equiv e _ _ fun l => ?_).symm
      rw [integral_indicator (hmeas' _), setIntegral_const, smul_eq_mul]
    · intro g _
      exact (integrable_const _).indicator (hmeas' g)
  refine ⟨V.card, fun l => μ.real {ω | (fun κ : T => σ κ ω) = (e l : T → Y)}, fun l => e l,
    fun l => measureReal_nonneg, ?_, hmean⟩
  have := hmean fun _ => 1
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at this
  exact this.symm

end Random

/-- **Paper: Proposition prop:random.** "Let w be a price on Y, let Q be a set disjoint from Y, and let σ be a random
map Y ∪ Q → Y that is the identity on Y, each σ(o) having finitely many values. Then a price on Y ∪ Q extends w and
satisfies |oo′| ≤ E |σ(o)σ(o′)| for all o, o′." -/
theorem prop_random {Y Q : Type} {w : Y → Y → ℝ} (hw : IsPrice K w) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (σ : Q → Ω → Y) (hfin : ∀ κ, (Set.range (σ κ)).Finite)
    (hmeas : ∀ κ y, MeasurableSet (σ κ ⁻¹' {y})) :
    ∃ w' : Y ⊕ Q → Y ⊕ Q → ℝ, IsPrice K w' ∧ (∀ y y', w' (Sum.inl y) (Sum.inl y') = w y y') ∧
      ∀ o o', w' o o' ≤
        ∫ ω, w (Sum.elim id (fun κ => σ κ ω) o) (Sum.elim id (fun κ => σ κ ω) o') ∂μ := by
  classical
  -- the two properties: at least w on Y, and at most the expectation
  let A : Y ⊕ Q → Y ⊕ Q → ℝ := fun o o' => match o, o' with
    | Sum.inl y, Sum.inl y' => w y y'
    | _, _ => 0
  let E : Y ⊕ Q → Y ⊕ Q → ℝ := fun o o' =>
    ∫ ω, w (Sum.elim id (fun κ => σ κ ω) o) (Sum.elim id (fun κ => σ κ ω) o') ∂μ
  suffices hS : ∀ S : Finset (Y ⊕ Q), ∃ d : S → S → ℝ, IsPrice K d ∧ ∀ a b : S, A a b ≤ d a b ∧ d a b ≤ E a b by
    obtain ⟨w', hw', h⟩ := prop_random_compact A E hS
    refine ⟨w', hw', fun y y' => le_antisymm ?_ (h (Sum.inl y) (Sum.inl y')).1, fun o o' => (h o o').2⟩
    simpa [E] using (h (Sum.inl y) (Sum.inl y')).2
  intro S
  -- Q₀: the new points of S; Y₀: the old points of S and all values of σ on Q₀
  let T : Finset Q := S.preimage Sum.inr Sum.inr_injective.injOn
  obtain ⟨m, θ, π, hθ, hθ1, hmean⟩ := prop_random_values μ σ hfin hmeas T
  let R : Finset Y := S.preimage Sum.inl Sum.inl_injective.injOn ∪
    Finset.univ.biUnion fun κ : T => Finset.univ.image fun l => π l κ
  have hR : ∀ l κ, π l κ ∈ R := fun l κ => Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨κ, Finset.mem_univ κ, Finset.mem_image_of_mem _ (Finset.mem_univ l)⟩)
  obtain ⟨v, hv, hv1, hv2⟩ := prop_random_limit (def_price_pullback hw (Subtype.val : R → Y)) θ hθ hθ1
    fun l κ => (⟨π l κ, hR l κ⟩ : R)
  -- the points of S among those of Y₀ ∪ Q₀, and their places under a map Q₀ → Y
  let g : S → R ⊕ T := fun a => match a with
    | ⟨Sum.inl y, hy⟩ => Sum.inl ⟨y, Finset.mem_union_left _ (Finset.mem_preimage.2 hy)⟩
    | ⟨Sum.inr κ, hκ⟩ => Sum.inr ⟨κ, Finset.mem_preimage.2 hκ⟩
  let place : (T → Y) → S → Y := fun f a => match a with
    | ⟨Sum.inl y, _⟩ => y
    | ⟨Sum.inr κ, hκ⟩ => f ⟨κ, Finset.mem_preimage.2 hκ⟩
  have hg : ∀ l (a : S), ((Sum.elim id (fun κ => (⟨π l κ, hR l κ⟩ : R)) (g a) : R) : Y) = place (π l) a := by
    rintro l ⟨y | κ, ha⟩ <;> rfl
  have hσ : ∀ ω (a : S), Sum.elim id (fun κ => σ κ ω) a.1 = place (fun κ : T => σ κ ω) a := by
    rintro ω ⟨y | κ, ha⟩ <;> rfl
  refine ⟨fun a b => v (g a) (g b), def_price_pullback hv g, fun a b => ⟨?_, ?_⟩⟩
  · obtain ⟨y | κ, ha⟩ := a <;> obtain ⟨y' | κ', hb⟩ := b
    · exact (hv1 ⟨y, _⟩ ⟨y', _⟩).ge
    all_goals exact hv.nonneg _ _
  · refine (hv2 (g a) (g b)).trans (le_of_eq ?_)
    show _ = ∫ ω, w (Sum.elim id (fun κ => σ κ ω) a.1) (Sum.elim id (fun κ => σ κ ω) b.1) ∂μ
    simp only [hg, hσ]
    exact (hmean fun f => w (place f a) (place f b)).symm

/-- Proposition prop:random for a random map with finitely many values σ_l, taken with probabilities θ_l. -/
theorem prop_random_finite {Y Q : Type} {w : Y → Y → ℝ} (hw : IsPrice K w) {Λ : Type} [Fintype Λ] (θ : Λ → ℝ)
    (hθ : ∀ l, 0 ≤ θ l) (hθ1 : ∑ l, θ l = 1) (σ : Λ → Q → Y) :
    ∃ w' : Y ⊕ Q → Y ⊕ Q → ℝ, IsPrice K w' ∧ (∀ y y', w' (Sum.inl y) (Sum.inl y') = w y y') ∧
      ∀ o o', w' o o' ≤ ∑ l, θ l * w (Sum.elim id (σ l) o) (Sum.elim id (σ l) o') := by
  classical
  let _ : MeasurableSpace Λ := ⊤
  have : MeasurableSingletonClass Λ := ⟨fun _ => trivial⟩
  let p : PMF Λ := PMF.ofFintype (fun l => ENNReal.ofReal (θ l))
    (by rw [← ENNReal.ofReal_sum_of_nonneg fun l _ => hθ l, hθ1, ENNReal.ofReal_one])
  obtain ⟨w', h1, h2, h3⟩ := prop_random hw p.toMeasure (fun κ l => σ l κ) (fun κ => Set.toFinite _)
    fun κ y => trivial
  refine ⟨w', h1, h2, fun o o' => (h3 o o').trans (le_of_eq ?_)⟩
  rw [PMF.integral_eq_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (hθ l), smul_eq_mul]

/-- **Paper: Lemma lem:hubs.** "Let I = I₁ ⊔ I₂, let a tensor t on I be a sum of r products of a tensor on I₁ and one
on I₂, and let n_p be its index sizes. For two further parties o₁, o₂ it is a restriction of
∏_{p ∈ I₁} ⟨n_p⟩_{p o₁} · ⟨r⟩_{o₁ o₂} · ∏_{p ∈ I₂} ⟨n_p⟩_{p o₂}, and this remains true when o₁, o₂ are identified with given
parties." In Lean the paper's I is A, its part I₁ is given by the predicate S, and α j, β j are the factors of the j-th
product, functions of the indices in I₁ and in I₂. The map π places the parties of A among those of a set I that also
contains o₁ and o₂, in any way; lem_hubs_further is the case of two further parties. -/
theorem lem_hubs {A : Type} [Fintype A] [DecidableEq A] (π : A → I) (t : Ten K A) (S : A → Prop) [DecidablePred S]
    {r : ℕ} (α β : Fin r → (∀ a, t.ι a) → K)
    (hα : ∀ j x x', (∀ a, S a → x a = x' a) → α j x = α j x')
    (hβ : ∀ j x x', (∀ a, ¬ S a → x a = x' a) → β j x = β j x')
    (hs : ∀ x, t.val x = ∑ j, α j x * β j x) (o₁ o₂ : I) :
    Restr (Ten.push π t)
      (Ten.prod (fun a => Ten.wire K (Fintype.card (t.ι a)) (π a) (if S a then o₁ else o₂)) * Ten.wire K r o₁ o₂) := by
  classical
  let Λ : Option A → Type := fun o => match o with
    | none => Fin r
    | some a => t.ι a
  let iΛ : ∀ o, Fintype (Λ o) := fun o => match o with
    | none => inferInstanceAs (Fintype (Fin r))
    | some a => t.fin a
  let ξ : A ⊕ Bool → I := Sum.elim π fun b => if b then o₁ else o₂
  let src : Option A → A ⊕ Bool := fun o => o.elim (Sum.inr true) Sum.inl
  let tgt : Option A → A ⊕ Bool := fun o => o.elim (Sum.inr false) fun a => Sum.inr (decide (S a))
  let tab : A ⊕ Bool → (∀ a, t.ι a) → (∀ o, Λ o) → K := fun v x l => match v with
    | Sum.inl a => if x a = l (some a) then 1 else 0
    | Sum.inr true => α (l none) fun a => l (some a)
    | Sum.inr false => β (l none) fun a => l (some a)
  have key := Restr.of_edges π ξ t Λ src tgt tab (by
    rintro (a | b) x x' l l' hx hl
    · have h1 := hx a rfl
      have h2 : l (some a) = l' (some a) := hl (some a) (Or.inl rfl)
      show (if x a = l (some a) then (1 : K) else 0) = if x' a = l' (some a) then 1 else 0
      rw [h1, h2]
    · cases b
      · have h1 : l none = l' none := hl none (Or.inr rfl)
        show β (l none) _ = β (l' none) _
        rw [h1]
        refine hβ _ _ _ fun a ha => hl (some a) (Or.inr ?_)
        show Sum.inr (decide (S a)) = _
        simp [ha]
      · have h1 : l none = l' none := hl none (Or.inl rfl)
        show α (l none) _ = α (l' none) _
        rw [h1]
        refine hα _ _ _ fun a ha => hl (some a) (Or.inr ?_)
        show Sum.inr (decide (S a)) = _
        simp [ha]) (by
    intro x
    have e1 : ∀ l : ∀ o, Λ o, ∏ v, tab v x l =
        (∏ a, if x a = l (some a) then (1 : K) else 0) *
          (α (l none) (fun a => l (some a)) * β (l none) fun a => l (some a)) := by
      intro l
      rw [Fintype.prod_sum_type]
      congr 1
      rw [Fintype.prod_bool]
    simp only [e1]
    rw [hs]
    symm
    refine (Fintype.sum_equiv (Equiv.piOptionEquivProd (β := Λ)) _
      (fun z : Λ none × (∀ a, Λ (some a)) => (∏ a, if x a = z.2 a then (1 : K) else 0) *
          (α z.1 z.2 * β z.1 z.2)) fun l => rfl).trans ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      obtain ⟨a, ha⟩ := Function.ne_iff.1 hy
      rw [Finset.prod_eq_zero (Finset.mem_univ a) (if_neg fun hxy => ha hxy.symm), zero_mul]
    · simp)
  refine key.trans ((Equi.prod_reindex _ (Equiv.optionEquivSumPUnit A).symm).1.trans
    ((Equi.prod_sum _).1.trans (Restr.mul (Restr.prod fun a => ?_) ((Equi.prod_unique _).1.trans ?_))))
  · show Restr (Ten.wire K (Fintype.card (t.ι a)) (π a) (if decide (S a) then o₁ else o₂)) _
    simp only [decide_eq_true_eq]
    exact Restr.refl _
  · show Restr (Ten.wire K (Fintype.card (Fin r)) o₁ o₂) _
    rw [Fintype.card_fin]
    exact Restr.refl _

/-- Lemma lem:hubs as printed, "for two further parties o₁, o₂": the parties are I₁ ⊔ I₂ and the two hubs. -/
theorem lem_hubs_further {I₁ I₂ : Type} [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    (t : Ten K (I₁ ⊕ I₂)) {r : ℕ} (α : Fin r → (∀ p, t.ι (Sum.inl p)) → K) (β : Fin r → (∀ p, t.ι (Sum.inr p)) → K)
    (hs : ∀ x, t.val x = ∑ j, α j (fun p => x (Sum.inl p)) * β j fun p => x (Sum.inr p)) :
    Restr (Ten.push (Sum.inl : I₁ ⊕ I₂ → (I₁ ⊕ I₂) ⊕ Bool) t)
      (Ten.prod (fun p : I₁ => Ten.wire K (Fintype.card (t.ι (Sum.inl p))) (Sum.inl (Sum.inl p)) (Sum.inr true)) *
        Ten.wire K r (Sum.inr true) (Sum.inr false) *
        Ten.prod fun p : I₂ => Ten.wire K (Fintype.card (t.ι (Sum.inr p))) (Sum.inl (Sum.inr p)) (Sum.inr false)) := by
  have key := lem_hubs (Sum.inl : I₁ ⊕ I₂ → (I₁ ⊕ I₂) ⊕ Bool) t (fun a => a.isLeft = true)
    (fun j x => α j fun p => x (Sum.inl p)) (fun j x => β j fun p => x (Sum.inr p))
    (fun j x x' h => congrArg (α j) (funext fun p => h (Sum.inl p) rfl))
    (fun j x x' h => congrArg (β j) (funext fun p => h (Sum.inr p) (by simp))) hs (Sum.inr true) (Sum.inr false)
  refine key.trans ((Restr.mul (Equi.prod_sum _).1 (Restr.refl _)).trans ?_)
  exact ((Equi.mul_assoc _ _ _).trans (((Equi.refl _).mul (Equi.mul_comm _ _)).trans (Equi.mul_assoc _ _ _).symm)).1

end Paper
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Lemmas for the crossing inequality

For Paper.prop_crossing (Paper/Crossing.lean): tensors with four legs, the two wires among them, and the compact set of the
pairs (r, l).
-/

namespace Nc.Price

open Ov Ov.Ten Finset

/-- `f` is a sum of `r` products of a function of the first two indices and one of the last two. -/
def SplitAB {K : Type} [Field K] {α β : Type} (f : α → β → α → β → K) (r : ℕ) : Prop :=
  ∃ g h : Fin r → α × β → K, ∀ a b c d, f a b c d = ∑ k, g k (a, b) * h k (c, d)

/-- `f` is a sum of `r` products of a function of the first and the last index and one of the two in the middle. -/
def SplitAD {K : Type} [Field K] {α β : Type} (f : α → β → α → β → K) (r : ℕ) : Prop :=
  ∃ (g : Fin r → α × β → K) (h : Fin r → β × α → K), ∀ a b c d, f a b c d = ∑ k, g k (a, d) * h k (b, c)

section Four

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]
variable {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β]
  [Nonempty β]

/-- A tensor with four legs, of sizes |α|, |β|, |α|, |β|. -/
def four (f : α → β → α → β → K) : Ten K (Fin 4) where
  ι q := match q with
    | 0 => α
    | 1 => β
    | 2 => α
    | 3 => β
  fin q := match q with
    | 0 => inferInstanceAs (Fintype α)
    | 1 => inferInstanceAs (Fintype β)
    | 2 => inferInstanceAs (Fintype α)
    | 3 => inferInstanceAs (Fintype β)
  dec q := match q with
    | 0 => inferInstanceAs (DecidableEq α)
    | 1 => inferInstanceAs (DecidableEq β)
    | 2 => inferInstanceAs (DecidableEq α)
    | 3 => inferInstanceAs (DecidableEq β)
  val x := f (x 0) (x 1) (x 2) (x 3)

variable (F : Spec K I)

/-- The two wires between x and v and between y and u. -/
theorem le_F_cross (x y v u : I) :
    (Fintype.card α : ℝ) ^ F.e x v * (Fintype.card β : ℝ) ^ F.e y u ≤
      F.F (Ten.push ![x, y, v, u]
        (four fun (a : α) (b : β) c d => if a = c ∧ b = d then (1 : K) else 0)) := by
  classical
  set D := Fintype.card α with hD
  set D' := Fintype.card β with hD'
  rw [← F.wire_eq x v (n := D) Fintype.card_pos, ← F.wire_eq y u (n := D') Fintype.card_pos,
    ← F.mul]
  refine F.mono ?_
  let e : Fin D ≃ α := (Fintype.equivFin α).symm
  let e' : Fin D' ≃ β := (Fintype.equivFin β).symm
  let σ : Fin 2 ⊕ Fin 2 → Fin 4 := Sum.elim ![0, 2] ![1, 3]
  let t : Ten K (Fin 2 ⊕ Fin 2) := outer₂ (unit K (Fin 2) D) (unit K (Fin 2) D')
  have h1 : (Sum.elim ![x, v] ![y, u] : Fin 2 ⊕ Fin 2 → I) = ![x, y, v, u] ∘ σ := by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  have h2 := (Equi.push_outer₂ (Sum.elim ![x, v] ![y, u]) (unit K (Fin 2) D) (unit K (Fin 2) D')).2
  refine Restr.trans h2 ?_
  rw [h1]
  refine (Equi.push_push ![x, y, v, u] σ t).2.trans (Restr.push _ ?_)
  refine Restr.of_map' (fun q => match q with
    | 0 => fun a => e (a ⟨Sum.inl 0, rfl⟩)
    | 1 => fun a => e' (a ⟨Sum.inr 0, rfl⟩)
    | 2 => fun a => e (a ⟨Sum.inl 1, rfl⟩)
    | 3 => fun a => e' (a ⟨Sum.inr 1, rfl⟩)) fun z => ?_
  have gen : ∀ (a0 a2 : Fin D) (a1 a3 : Fin D'),
      (if a0 = a2 then (1 : K) else 0) * (if a1 = a3 then 1 else 0) =
        if e a0 = e a2 ∧ e' a1 = e' a3 then 1 else 0 := by
    intro a0 a2 a1 a3
    simp only [e.injective.eq_iff, e'.injective.eq_iff]
    rw [ite_and, ite_mul, one_mul, zero_mul]
  exact (congr_arg₂ (· * ·) (unit_two_val fun l => z (σ (Sum.inl l)) ⟨Sum.inl l, rfl⟩)
    (unit_two_val fun l => z (σ (Sum.inr l)) ⟨Sum.inr l, rfl⟩)).trans (gen _ _ _ _)

end Four

theorem rpow_le_exp (r : ℕ) (z : ℝ) : (r : ℝ) ^ z ≤ Real.exp (Real.log r * z) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp only [Nat.cast_zero, Real.log_zero, zero_mul, Real.exp_zero]
    exact Real.zero_rpow_le_one z
  · rw [Real.rpow_def_of_pos (by exact_mod_cast hr)]

/-- The quarter disc of radius √ρ. -/
def quarter (ρ : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ ρ}

theorem isCompact_quarter (ρ : ℝ) : IsCompact (quarter ρ) := by
  have h1 : IsCompact (Set.Icc (0 : ℝ) (ρ + 1) ×ˢ Set.Icc (0 : ℝ) (ρ + 1)) :=
    isCompact_Icc.prod isCompact_Icc
  refine h1.of_isClosed_subset ?_ ?_
  · have h2 : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} := isClosed_le continuous_const continuous_fst
    have h3 : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} := isClosed_le continuous_const continuous_snd
    have h4 : IsClosed {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ ρ} :=
      isClosed_le (by fun_prop) continuous_const
    exact h2.inter (h3.inter h4)
  · rintro ⟨r, l⟩ ⟨hr, hl, h⟩
    simp only at hr hl h
    refine ⟨⟨hr, ?_⟩, ⟨hl, ?_⟩⟩ <;> nlinarith [sq_nonneg (r - 1), sq_nonneg (l - 1)]

/-- If X ≤ min(A + r·s, B + l·t) + δ for all δ > 0 with some (r, l) in the quarter disc, then also for
δ = 0. -/
theorem exists_quarter {ρ X A B s t : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ δ : ℝ, 0 < δ → ∃ p ∈ quarter ρ, X ≤ min (A + p.1 * s) (B + p.2 * t) + δ) :
    ∃ p ∈ quarter ρ, X ≤ min (A + p.1 * s) (B + p.2 * t) := by
  obtain ⟨p, hp, hmax⟩ := (isCompact_quarter ρ).exists_isMaxOn
    (f := fun p : ℝ × ℝ => min (A + p.1 * s) (B + p.2 * t))
    ⟨(0, 0), le_rfl, le_rfl, by simpa using hρ⟩ (by fun_prop)
  refine ⟨p, hp, le_of_forall_pos_le_add fun δ hδ => ?_⟩
  obtain ⟨p', hp', h'⟩ := h δ hδ
  have hm : min (A + p'.1 * s) (B + p'.2 * t) ≤ min (A + p.1 * s) (B + p.2 * t) := hmax hp'
  linarith

end Nc.Price
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Two crossing wires": the inequality

The states are in Paper/States.lean (Lemma lem:count) and the identity is in Paper/Identity.lean (Proposition prop:identity).
-/

namespace Paper

open Finset Filter Ov Ov.Ten Nc.Price Nc.Cross

variable {K : Type} [Field K]

section Hubs

variable {I : Type} [Fintype I] [DecidableEq I] (F : Spec K I)

/-- Lemma lem:hubs, read for a spectral point φ: a tensor that is a sum of r products of a tensor on the legs in S and one on the
other legs has φ at most the product of the values of the wires to the hubs o₁, o₂ and of the wire ⟨r⟩ between them. -/
theorem prop_crossing_cut {A : Type} [Fintype A] [DecidableEq A] (π : A → I) (t : Ten K A) (S : A → Prop)
    [DecidablePred S] {r : ℕ} (g h : Fin r → (∀ a, t.ι a) → K)
    (hg : ∀ j x x', (∀ a, S a → x a = x' a) → g j x = g j x')
    (hh : ∀ j x x', (∀ a, ¬ S a → x a = x' a) → h j x = h j x')
    (hs : ∀ x, t.val x = ∑ j, g j x * h j x) (o₁ o₂ : I) :
    F.F (Ten.push π t) ≤ (∏ a, (Fintype.card (t.ι a) : ℝ) ^ F.e (π a) (if S a then o₁ else o₂)) *
      (r : ℝ) ^ F.e o₁ o₂ := by
  refine (F.mono (lem_hubs π t S g h hg hh hs o₁ o₂)).trans ?_
  rw [F.mul, F.prod]
  exact mul_le_mul (Finset.prod_le_prod (fun _ _ => F.nonneg _) fun a _ => F.wire_le _ _ _) (F.wire_le _ _ _)
    (F.nonneg _) (Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

variable {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β]
  [Nonempty β]

/-- Proof of Proposition prop:crossing: "Lemma lem:hubs, with the hubs o, o′ for (c) …, bounds φ(Ψ_N)." The four legs are at
x, y, v, u, and f is a sum of R products of a function of the indices at x, y and one of those at v, u. -/
theorem prop_crossing_hubs_c {f : α → β → α → β → K} {R : ℕ} (h : SplitAB f R) (x y v u o o' : I) :
    F.F (Ten.push ![x, y, v, u] (four f)) ≤
      (Fintype.card α : ℝ) ^ (F.e x o + F.e v o') * (Fintype.card β : ℝ) ^ (F.e y o + F.e u o') *
        (R : ℝ) ^ F.e o o' := by
  obtain ⟨g, w, hf⟩ := h
  have h1 := prop_crossing_cut F ![x, y, v, u] (four f) (fun a => a = 0 ∨ a = 1)
    (fun t z => g t (z 0, z 1)) (fun t z => w t (z 2, z 3))
    (fun t z z' hz => by
      have h0 := hz 0 (Or.inl rfl)
      have h1 := hz 1 (Or.inr rfl)
      simp only [h0, h1])
    (fun t z z' hz => by
      have h0 := hz 2 (by decide)
      have h1 := hz 3 (by decide)
      simp only [h0, h1])
    (fun z => hf (z 0) (z 1) (z 2) (z 3)) o o'
  refine h1.trans (mul_le_mul_of_nonneg_right (le_of_eq ?_) (by positivity))
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  rw [Fin.prod_univ_four, Real.rpow_add hα, Real.rpow_add hβ]
  show (Fintype.card α : ℝ) ^ F.e x o * (Fintype.card β : ℝ) ^ F.e y o *
    (Fintype.card α : ℝ) ^ F.e v o' * (Fintype.card β : ℝ) ^ F.e u o' = _
  ring

/-- Proof of Proposition prop:crossing: "Lemma lem:hubs, with the hubs … w, w′ for (b), bounds φ(Ψ_N)." Here f is a sum of L
products of a function of the indices at x, u and one of those at y, v. -/
theorem prop_crossing_hubs_b {f : α → β → α → β → K} {L : ℕ} (h : SplitAD f L) (x y v u w w' : I) :
    F.F (Ten.push ![x, y, v, u] (four f)) ≤
      (Fintype.card α : ℝ) ^ (F.e x w + F.e v w') * (Fintype.card β : ℝ) ^ (F.e u w + F.e y w') *
        (L : ℝ) ^ F.e w w' := by
  obtain ⟨g, m, hf⟩ := h
  have h1 := prop_crossing_cut F ![x, y, v, u] (four f) (fun a => a = 0 ∨ a = 3)
    (fun t z => g t (z 0, z 3)) (fun t z => m t (z 1, z 2))
    (fun t z z' hz => by
      have h0 := hz 0 (Or.inl rfl)
      have h1 := hz 3 (Or.inr rfl)
      simp only [h0, h1])
    (fun t z z' hz => by
      have h0 := hz 1 (by decide)
      have h1 := hz 2 (by decide)
      simp only [h0, h1])
    (fun z => hf (z 0) (z 1) (z 2) (z 3)) w w'
  refine h1.trans (mul_le_mul_of_nonneg_right (le_of_eq ?_) (by positivity))
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  rw [Fin.prod_univ_four, Real.rpow_add hα, Real.rpow_add hβ]
  show (Fintype.card α : ℝ) ^ F.e x w * (Fintype.card β : ℝ) ^ F.e y w' *
    (Fintype.card α : ℝ) ^ F.e v w' * (Fintype.card β : ℝ) ^ F.e u w = _
  ring

/-- Proof of Proposition prop:crossing: "The product of the two wires is covered by the Θ+1 tensors Ψ_N of Proposition
prop:identity (a), φ is subadditive". The left side is the value of φ at the two wires, of dimensions |α| and |β|. -/
theorem prop_crossing_cover {J : Type} [Fintype J] (Ψ : J → α → β → α → β → K)
    (hΨ : ∀ a b c d, ∑ j, Ψ j a b c d = if a = c ∧ b = d then 1 else 0) (x y v u : I) :
    (Fintype.card α : ℝ) ^ F.e x v * (Fintype.card β : ℝ) ^ F.e y u ≤
      ∑ j, F.F (Ten.push ![x, y, v, u] (four (Ψ j))) := by
  refine (le_F_cross (K := K) (α := α) (β := β) F x y v u).trans ?_
  have h : SumRestr (four fun (a : α) (b : β) c d => if a = c ∧ b = d then (1 : K) else 0)
      fun j => four (Ψ j) :=
    SumRestr.of_withVal (four fun (a : α) (b : β) c d => if a = c ∧ b = d then (1 : K) else 0)
      (fun j z => Ψ j (z 0) (z 1) (z 2) (z 3)) fun z => (hΨ (z 0) (z 1) (z 2) (z 3)).symm
  exact F.le_sum _ _ (h.push ![x, y, v, u])

/-- Proof of Proposition prop:crossing: "so some N has ln φ(Ψ_N) ≥ (p|xv| + q|yu| − o(1))κ√n₀". Before logarithms: some φ(Ψ_N) is
at least the value of the two wires divided by the number Θ+1 of the tensors. -/
theorem prop_crossing_some {J : Type} [Fintype J] (Ψ : J → α → β → α → β → K)
    (hΨ : ∀ a b c d, ∑ j, Ψ j a b c d = if a = c ∧ b = d then 1 else 0) (x y v u : I) :
    ∃ j, (Fintype.card α : ℝ) ^ F.e x v * (Fintype.card β : ℝ) ^ F.e y u ≤
      Fintype.card J * F.F (Ten.push ![x, y, v, u] (four (Ψ j))) := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have h1 := prop_crossing_cover F Ψ hΨ x y v u
  have hJ : Nonempty J := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact absurd h1 (not_le.2 (mul_pos (Real.rpow_pos_of_pos hα _) (Real.rpow_pos_of_pos hβ _)))
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image (Finset.univ : Finset J)
    (fun j => F.F (Ten.push ![x, y, v, u] (four (Ψ j)))) Finset.univ_nonempty
  refine ⟨j, h1.trans ?_⟩
  rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  exact Finset.sum_le_sum fun i hi => hj i hi

/-- Proof of Proposition prop:crossing: "Lemma lem:hubs, with the hubs o, o′ for (c) and w, w′ for (b), bounds φ(Ψ_N) in both ways."
So for the N of the step before, in logarithms: ln|α|·|xv| + ln|β|·|yu| is at most ln(Θ+1) plus each of the two bounds through the
hubs, where Ψ_N is a sum of R_N products as in (c) and of L_N products as in (b). -/
theorem prop_crossing_term {J : Type} [Fintype J] (Ψ : J → α → β → α → β → K) (R L : J → ℕ)
    (hR : ∀ j, SplitAB (Ψ j) (R j))
    (hL : ∀ j, SplitAD (Ψ j) (L j))
    (hΨ : ∀ a b c d, ∑ j, Ψ j a b c d = if a = c ∧ b = d then 1 else 0)
    (x y v u o o' w w' : I) :
    ∃ j, Real.log (Fintype.card α) * F.e x v + Real.log (Fintype.card β) * F.e y u ≤
      Real.log (Fintype.card J) +
      min (Real.log (Fintype.card α) * (F.e x o + F.e v o') +
          Real.log (Fintype.card β) * (F.e y o + F.e u o') + Real.log (R j) * F.e o o')
        (Real.log (Fintype.card α) * (F.e x w + F.e v w') +
          Real.log (Fintype.card β) * (F.e u w + F.e y w') + Real.log (L j) * F.e w w') := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  obtain ⟨j, hj⟩ := prop_crossing_some F Ψ hΨ x y v u
  have hJ0 : (0 : ℝ) < Fintype.card J := by
    have : Nonempty J := ⟨j⟩
    exact_mod_cast Fintype.card_pos
  refine ⟨j, ?_⟩
  have hexp : ∀ (s s' : ℝ) (n : ℕ) (e : ℝ), (Fintype.card α : ℝ) ^ s * (Fintype.card β : ℝ) ^ s' * (n : ℝ) ^ e ≤
      Real.exp (Real.log (Fintype.card α) * s + Real.log (Fintype.card β) * s' + Real.log n * e) := by
    intro s s' n e
    rw [Real.rpow_def_of_pos hα, Real.rpow_def_of_pos hβ, Real.exp_add, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (rpow_le_exp n e) (by positivity)
  have hc := (prop_crossing_hubs_c F (hR j) x y v u o o').trans (hexp _ _ _ _)
  have hb := (prop_crossing_hubs_b F (hL j) x y v u w w').trans (hexp _ _ _ _)
  have hm := le_min hc hb
  rw [← Real.exp_monotone.map_min] at hm
  have h2 := hj.trans (mul_le_mul_of_nonneg_left hm hJ0.le)
  rw [Real.rpow_def_of_pos hα, Real.rpow_def_of_pos hβ, ← Real.exp_add] at h2
  nth_rewrite 1 [← Real.exp_log hJ0] at h2
  rw [← Real.exp_add, Real.exp_le_exp] at h2
  exact h2

end Hubs

/-- Proof of Proposition prop:crossing: "By pigeonhole some classes Σ_i of energy e_i ≤ E_i contain at least a fraction (E_i+1)⁻²,
and of course at most all, of the states of energy at most E_i." -/
theorem prop_crossing_classes (E : ℕ) : ∃ μ e, e ≤ E ∧ stateCount E ≤ (E + 1) ^ 2 * (states μ e).card ∧
    (states μ e).card ≤ stateCount E := by
  classical
  set S := range (E + 1) ×ˢ range (E + 1) with hS
  have hmaps : ∀ s ∈ pairs E, (s.1.card, en s.1 + en s.2) ∈ S := by
    intro s hs
    obtain ⟨h1, h2⟩ := mem_pairs.1 hs
    have h3 : s.1.card ≤ en s.1 := by
      rw [en, Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun i _ => by omega
    rw [hS, mem_product, mem_range, mem_range]
    exact ⟨by simp only; omega, by simp only; omega⟩
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image S (fun z => (states z.1 z.2).card) ⟨(0, 0), by simp [hS]⟩
  have hzE : z.2 ≤ E := by
    have := (mem_product.1 hz).2
    rw [mem_range] at this
    omega
  refine ⟨z.1, z.2, hzE, ?_, card_le_card ((filter_subset _ _).trans (pairs_mono hzE))⟩
  show (pairs E).card ≤ _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ b ∈ S, ((pairs E).filter fun s => (s.1.card, en s.1 + en s.2) = b).card
      ≤ ∑ b ∈ S, (states b.1 b.2).card := by
        refine Finset.sum_le_sum fun b _ => Finset.card_le_card fun s hs => ?_
        obtain ⟨h1, h2⟩ := mem_filter.1 hs
        obtain ⟨h3, h4⟩ := mem_pairs.1 h1
        rw [← h2]
        exact mem_filter.2 ⟨mem_pairs.2 ⟨h3, le_rfl⟩, rfl, h3.symm, rfl⟩
    _ ≤ ∑ _b ∈ S, (states z.1 z.2).card := Finset.sum_le_sum fun b hb => hmax b hb
    _ = (E + 1) ^ 2 * (states z.1 z.2).card := by
        rw [Finset.sum_const, smul_eq_mul, hS, card_product, card_range, pow_two]

/-- Proof of Proposition prop:crossing: "so, in units of κ√n₀, their logarithms are p + o(1) and q + o(1) by Lemma lem:count."
Here κ is a constant with the two properties of Lemma lem:count, n is the paper's n₀, and the class Σ of size μ and energy
e ≤ E = ⌊p²n⌋ is the one found by pigeonhole. -/
theorem prop_crossing_class_size {κ : ℝ} (hκ : 0 < κ) (hup : ∀ E : ℕ, Real.log (stateCount E) ≤ κ * √E)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ E : ℕ in atTop, (κ - ε) * √E ≤ Real.log (stateCount E)) {p : ℝ} (hp : 0 ≤ p)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∃ μ e, e ≤ ⌊p ^ 2 * n⌋₊ ∧ 0 < (states μ e).card ∧
      |Real.log (states μ e).card - p * (κ * √n)| ≤ δ * (κ * √n) := by
  have hlow' : ∀ ε > 0, ∃ E₀ : ℕ, ∀ E, E₀ ≤ E → (κ - ε) * √E ≤ lp E := fun ε hε => eventually_atTop.1 (hlow ε hε)
  filter_upwards [lower_bound hκ hlow' hp (η := δ * κ) (by positivity)] with n hn
  obtain ⟨μ, e, he, hcard, hle⟩ := prop_crossing_classes ⌊p ^ 2 * n⌋₊
  set E := ⌊p ^ 2 * n⌋₊ with hE
  have hpos : 0 < (states μ e).card := by
    rcases Nat.eq_zero_or_pos (states μ e).card with h0 | h0
    · rw [h0, mul_zero] at hcard
      exact absurd (pairs_pos E) (by simpa [stateCount] using hcard)
    · exact h0
  have h0 : (0 : ℝ) < (states μ e).card := by exact_mod_cast hpos
  have hlower : lp E - 2 * Real.log ((E : ℝ) + 1) ≤ Real.log (states μ e).card := by
    have h1 : ((pairs E).card : ℝ) ≤ ((E : ℝ) + 1) ^ 2 * (states μ e).card := by exact_mod_cast hcard
    have h2 := Real.log_le_log (by exact_mod_cast pairs_pos E) h1
    rw [Real.log_mul (by positivity) h0.ne', Real.log_pow] at h2
    rw [Nc.Cross.lp]
    push_cast at h2
    linarith
  have hupper : Real.log (states μ e).card ≤ κ * √(E : ℝ) :=
    (Real.log_le_log h0 (by exact_mod_cast hle)).trans (hup E)
  have hv := mul_le_mul_of_nonneg_left (sqrt_floor_le hp n) hκ.le
  have hd : 0 ≤ δ * (κ * √(n : ℝ)) := by positivity
  refine ⟨μ, e, he, hpos, abs_le.2 ⟨?_, ?_⟩⟩
  · linarith
  · linarith

/-- Proof of Proposition prop:crossing: "In the same units the logarithm of the number of products in (b) is at most l + o(1) and
that in (c) at most r + o(1), with l² = N/n₀, r² = (Θ−N)/n₀". Here M stands for N and for Θ − N, which are at most Θ ≤ An, and
(M+1)P(M) is the number of products. -/
theorem prop_crossing_products {κ : ℝ} (hκ : 0 < κ) (hup : ∀ E : ℕ, Real.log (stateCount E) ≤ κ * √E) {A : ℝ}
    (hA : 0 ≤ A) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ M : ℕ, (M : ℝ) ≤ A * n →
      Real.log (((M + 1) * stateCount M : ℕ) : ℝ) ≤ (√(M : ℝ) / √(n : ℝ) + δ) * (κ * √n) := by
  filter_upwards [log_small hA (η := δ * κ) (by positivity), eventually_ge_atTop 1] with n hlog hn M hM
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have h2 : Real.log ((M : ℝ) + 1) ≤ δ * κ * √(n : ℝ) :=
    (Real.log_le_log (by positivity) (by linarith)).trans hlog
  have h4 : Real.log (((M + 1) * stateCount M : ℕ) : ℝ) = Real.log ((M : ℝ) + 1) + Real.log (stateCount M) := by
    push_cast
    exact Real.log_mul (by positivity) (by exact_mod_cast (pairs_pos M).ne')
  have h5 : (√(M : ℝ) / √(n : ℝ) + δ) * (κ * √(n : ℝ)) = κ * √(M : ℝ) + δ * κ * √(n : ℝ) := by
    field_simp
  rw [h5, h4]
  linarith [hup M]

/-- Proof of Proposition prop:crossing, the tensors: for every δ > 0 there are s > 0 and finite sets α, β (in the proof: the
paper's κ√n₀ and the classes of states, by pigeonhole and Lemma lem:count) with ln|α| = (p ± δ)s and ln|β| = (q ± δ)s, and
at most e^(δs) tensors Ψ_N with sum the two wires (Proposition prop:identity (a)), where Ψ_N is a sum of at most e^((r+δ)s) products as in (c) and of at most e^((l+δ)s)
products as in (b), with r² + l² ≤ 2(p² + q²). -/
theorem prop_crossing_tensors (K : Type) [Field K] {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (α β J : Type) (_ : Fintype α) (_ : DecidableEq α) (_ : Nonempty α)
      (_ : Fintype β) (_ : DecidableEq β) (_ : Nonempty β) (_ : Fintype J)
      (Ψ : J → α → β → α → β → K) (R L : J → ℕ) (s : ℝ), 0 < s ∧
      (∀ j, SplitAB (Ψ j) (R j)) ∧ (∀ j, SplitAD (Ψ j) (L j)) ∧
      (∀ a b c d, ∑ j, Ψ j a b c d = if a = c ∧ b = d then 1 else 0) ∧
      Real.log (Fintype.card J) ≤ δ * s ∧ |Real.log (Fintype.card α) - p * s| ≤ δ * s ∧
      |Real.log (Fintype.card β) - q * s| ≤ δ * s ∧
      ∀ j, ∃ r l : ℝ, 0 ≤ r ∧ 0 ≤ l ∧ r ^ 2 + l ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) ∧
        Real.log (R j) ≤ (r + δ) * s ∧ Real.log (L j) ≤ (l + δ) * s := by
  obtain ⟨c, hc, hup, hlow⟩ := lem_count
  set A : ℝ := 2 * (p ^ 2 + q ^ 2) with hA
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨n, ⟨⟨μ, e₁, he₁, hpos₁, hsize₁⟩, ⟨ν, e₂, he₂, hpos₂, hsize₂⟩⟩, hnum, hlog, hn⟩ :=
    (((prop_crossing_class_size hc hup hlow hp hδ).and (prop_crossing_class_size hc hup hlow hq hδ)).and
      ((prop_crossing_products hc hup hA0 hδ).and
        ((log_small hA0 (η := δ * c) (by positivity)).and (eventually_ge_atTop 1)))).exists
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  obtain ⟨Ψ, hΨ, hL, hR⟩ := prop_identity μ ν e₁ e₂
  have hH : ((2 * (e₁ + e₂) : ℕ) : ℝ) ≤ A * n := by
    have h1 : ((e₁ : ℕ) : ℝ) ≤ (⌊p ^ 2 * n⌋₊ : ℕ) := by exact_mod_cast he₁
    have h2 : ((e₂ : ℕ) : ℝ) ≤ (⌊q ^ 2 * n⌋₊ : ℕ) := by exact_mod_cast he₂
    have h3 := floor_le' (p := p) n
    have h4 := floor_le' (p := q) n
    push_cast
    rw [hA]
    linarith
  have hnum' : ∀ M : ℕ, M ≤ 2 * (e₁ + e₂) →
      Real.log (((M + 1) * stateCount M : ℕ) : ℝ) ≤ (Real.sqrt M / Real.sqrt n + δ) * (c * Real.sqrt n) :=
    fun M hM => hnum M (le_trans (by exact_mod_cast hM) hH)
  refine ⟨↥(states μ e₁), ↥(states ν e₂), Fin (2 * (e₁ + e₂) + 1), inferInstance, inferInstance,
    ?_, inferInstance, inferInstance, ?_, inferInstance, fun N a b c d => ((Ψ N a b c d : ℤ) : K),
    fun N => (2 * (e₁ + e₂) - N + 1) * stateCount (2 * (e₁ + e₂) - N), fun N => (N + 1) * stateCount N,
    c * Real.sqrt n, by positivity, fun N => ?_, fun N => ?_, fun a b c d => ?_, ?_, ?_, ?_, fun N => ?_⟩
  · exact (Finset.card_pos.1 hpos₁).to_subtype
  · exact (Finset.card_pos.1 hpos₂).to_subtype
  · obtain ⟨g, h, hgh⟩ := hR N _ rfl
    refine ⟨fun k z => ((g k z : ℤ) : K), fun k z => ((h k z : ℤ) : K), fun a b c d => ?_⟩
    simp only
    rw [hgh]
    push_cast
    rfl
  · obtain ⟨g, h, hgh⟩ := hL N
    refine ⟨fun k z => ((g k z : ℤ) : K), fun k z => ((h k z : ℤ) : K), fun a b c d => ?_⟩
    simp only
    rw [hgh]
    push_cast
    rfl
  · rw [← Int.cast_sum, hΨ, ite_and]
    split_ifs <;> simp
  · rw [Fintype.card_fin]
    push_cast
    push_cast at hH
    have h1 : Real.log (2 * ((e₁ : ℝ) + e₂) + 1) ≤ Real.log (A * n + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  · rw [Fintype.card_coe]
    exact hsize₁
  · rw [Fintype.card_coe]
    exact hsize₂
  · have hN : (N : ℕ) ≤ 2 * (e₁ + e₂) := by omega
    refine ⟨Real.sqrt ((2 * (e₁ + e₂) - N : ℕ) : ℝ) / Real.sqrt n, Real.sqrt ((N : ℕ) : ℝ) / Real.sqrt n,
      by positivity, by positivity, ?_, hnum' _ (Nat.sub_le _ _), hnum' _ hN⟩
    rw [div_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg (2 * (e₁ + e₂) - N)),
      Real.sq_sqrt (Nat.cast_nonneg (N : ℕ)), Real.sq_sqrt hn0.le, ← add_div, div_le_iff₀ hn0, Nat.cast_sub hN, sub_add_cancel]
    exact hH

/-- Proof of Proposition prop:crossing: "So it suffices to treat d_φ for a spectral point φ"; this is the statement for d_φ. "A limit
of (r, l) along a subsequence proves the first statement." -/
theorem prop_crossing_spectral {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {I : Type} [Fintype I]
    [DecidableEq I] (F : Spec K I) (x y v u o o' w w' : I) :
    ∃ z ∈ quarter (2 * (p ^ 2 + q ^ 2)), p * F.e x v + q * F.e y u ≤
      min (p * F.e x o + q * F.e y o + p * F.e v o' + q * F.e u o' + z.1 * F.e o o')
        (p * F.e x w + q * F.e u w + q * F.e y w' + p * F.e v w' + z.2 * F.e w w') := by
  refine exists_quarter (by positivity) fun δ hδ => ?_
  obtain ⟨α, β, J, _, _, _, _, _, _, _, Ψ, R, L, s, hs, hR, hL, hΨ, hJ, hα, hβ, hrl⟩ :=
    prop_crossing_tensors K hp hq (δ := δ / 8) (by positivity)
  obtain ⟨j, hj⟩ := prop_crossing_term F Ψ R L hR hL hΨ x y v u o o' w w'
  obtain ⟨r, l, hr, hl, hrl, h1, h2⟩ := hrl j
  refine ⟨(r, l), ⟨hr, hl, hrl⟩, ?_⟩
  set A := Real.log (Fintype.card α) with hA
  set B := Real.log (Fintype.card β) with hB
  obtain ⟨hα1, hα2⟩ := abs_le.1 hα
  obtain ⟨hβ1, hβ2⟩ := abs_le.1 hβ
  have hi : ∀ (a b : I) {Z c : ℝ}, Z ≤ c * s + δ / 8 * s → Z * F.e a b ≤ (c * F.e a b + δ / 8) * s := by
    intro a b Z c h
    have e0 := F.e_nonneg a b
    have e1 := F.e_le_one a b
    have h3 := mul_le_mul_of_nonneg_right h e0
    have h4 : δ / 8 * s * F.e a b ≤ δ / 8 * s := mul_le_of_le_one_right (by positivity) e1
    nlinarith
  have lo : ∀ (a b : I) {Z c : ℝ}, c * s - δ / 8 * s ≤ Z → (c * F.e a b - δ / 8) * s ≤ Z * F.e a b := by
    intro a b Z c h
    have e0 := F.e_nonneg a b
    have e1 := F.e_le_one a b
    have h3 := mul_le_mul_of_nonneg_right h e0
    have h4 : δ / 8 * s * F.e a b ≤ δ / 8 * s := mul_le_of_le_one_right (by positivity) e1
    nlinarith
  have b1 := lo x v (Z := A) (c := p) (by linarith)
  have b2 := lo y u (Z := B) (c := q) (by linarith)
  rw [← min_add_add_right]
  refine le_min ?_ ?_
  · have hj1 := hj.trans (add_le_add le_rfl (min_le_left _ _))
    have c1 := hi x o (Z := A) (c := p) (by linarith)
    have c2 := hi y o (Z := B) (c := q) (by linarith)
    have c3 := hi v o' (Z := A) (c := p) (by linarith)
    have c4 := hi u o' (Z := B) (c := q) (by linarith)
    have c5 := hi o o' (Z := Real.log (R j)) (c := r) (by linarith)
    refine le_of_mul_le_mul_right ?_ hs
    simp only
    nlinarith
  · have hj1 := hj.trans (add_le_add le_rfl (min_le_right _ _))
    have c1 := hi x w (Z := A) (c := p) (by linarith)
    have c2 := hi u w (Z := B) (c := q) (by linarith)
    have c3 := hi v w' (Z := A) (c := p) (by linarith)
    have c4 := hi y w' (Z := B) (c := q) (by linarith)
    have c5 := hi w w' (Z := Real.log (L j)) (c := l) (by linarith)
    refine le_of_mul_le_mul_right ?_ hs
    simp only
    nlinarith

/-- Proposition prop:crossing, the first statement. "Pull the price back to eight distinct points; this covers coincidences. Both
inequalities are homogeneous in the distances, and the pairs (r, l) lie in a compact set, so they pass to limits." -/
theorem prop_crossing_first {Y : Type} {d : Y → Y → ℝ} (hd : IsPrice K d) (x v y u o o' w w' : Y)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ∃ r l : ℝ, 0 ≤ r ∧ 0 ≤ l ∧ r ^ 2 + l ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) ∧
      p * d x v + q * d y u ≤ p * d x o + q * d y o + p * d v o' + q * d u o' + r * d o o' ∧
      p * d x v + q * d y u ≤ p * d x w + q * d u w + q * d y w' + p * d v w' + l * d w w' := by
  set ρ := 2 * (p ^ 2 + q ^ 2) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  obtain ⟨z, ⟨h1, h2, h3⟩, h⟩ : ∃ z ∈ quarter ρ, p * d x v + q * d y u ≤
      min (p * d x o + q * d y o + p * d v o' + q * d u o' + z.1 * d o o')
        (p * d x w + q * d u w + q * d y w' + p * d v w' + z.2 * d w w') := by
    refine exists_quarter hρ0 fun δ hδ => ?_
    set T := 3 * (p + q) + ρ + 1 with hT
    have hT0 : 0 < T := by positivity
    set η := δ / T with hη
    have hη0 : 0 < η := by positivity
    have hηT : η * T = δ := by rw [hη]; field_simp
    obtain ⟨F, c, hc, hF⟩ := hd.exists_spec ![x, y, v, u, o, o', w, w'] hη0
    obtain ⟨z, hz, h⟩ := prop_crossing_spectral hp hq F 0 1 2 3 4 5 6 7
    refine ⟨z, hz, ?_⟩
    obtain ⟨hz1, hz2, hz3⟩ := hz
    have q1 : z.1 ≤ ρ + 1 := by nlinarith [sq_nonneg (z.1 - 1)]
    have q2 : z.2 ≤ ρ + 1 := by nlinarith [sq_nonneg (z.2 - 1)]
    have lo : ∀ (i j : Fin 8) {t : ℝ}, 0 ≤ t →
        t * (c * F.e i j) ≤ t * d (![x, y, v, u, o, o', w, w'] i) (![x, y, v, u, o, o', w, w'] j) +
          t * η := by
      intro i j t ht
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith [(abs_lt.1 (hF i j)).1]) ht
    have hi : ∀ (i j : Fin 8) {t : ℝ}, 0 ≤ t →
        t * d (![x, y, v, u, o, o', w, w'] i) (![x, y, v, u, o, o', w, w'] j) ≤
          t * (c * F.e i j) + t * η := by
      intro i j t ht
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith [(abs_lt.1 (hF i j)).2]) ht
    have a1 : p * d x v ≤ p * (c * F.e 0 2) + p * η := hi 0 2 hp
    have a2 : q * d y u ≤ q * (c * F.e 1 3) + q * η := hi 1 3 hq
    have a3 : p * (c * F.e 0 4) ≤ p * d x o + p * η := lo 0 4 hp
    have a4 : q * (c * F.e 1 4) ≤ q * d y o + q * η := lo 1 4 hq
    have a5 : p * (c * F.e 2 5) ≤ p * d v o' + p * η := lo 2 5 hp
    have a6 : q * (c * F.e 3 5) ≤ q * d u o' + q * η := lo 3 5 hq
    have a7 : z.1 * (c * F.e 4 5) ≤ z.1 * d o o' + z.1 * η := lo 4 5 hz1
    have a8 : p * (c * F.e 0 6) ≤ p * d x w + p * η := lo 0 6 hp
    have a9 : q * (c * F.e 3 6) ≤ q * d u w + q * η := lo 3 6 hq
    have b1 : q * (c * F.e 1 7) ≤ q * d y w' + q * η := lo 1 7 hq
    have b2 : p * (c * F.e 2 7) ≤ p * d v w' + p * η := lo 2 7 hp
    have b3 : z.2 * (c * F.e 6 7) ≤ z.2 * d w w' + z.2 * η := lo 6 7 hz2
    have c1 : z.1 * η ≤ (ρ + 1) * η := mul_le_mul_of_nonneg_right q1 hη0.le
    have c2 : z.2 * η ≤ (ρ + 1) * η := mul_le_mul_of_nonneg_right q2 hη0.le
    have hsum : 3 * (p * η) + 3 * (q * η) + (ρ + 1) * η = δ := by rw [← hηT, hT]; ring
    rw [← min_add_add_right]
    refine le_min ?_ ?_
    · have h4 := mul_le_mul_of_nonneg_left (h.trans (min_le_left _ _)) hc
      linarith
    · have h4 := mul_le_mul_of_nonneg_left (h.trans (min_le_right _ _)) hc
      linarith
  exact ⟨z.1, z.2, h1, h2, h3, le_min_iff.1 h⟩

/-- **Paper: Proposition prop:crossing.** "Let x, v, y, u, o, o′, w, w′ be points of a price and p, q ≥ 0. There are r, l ≥ 0 with
r² + l² ≤ 2(p² + q²) such that p|xv| + q|yu| is at most each of p|xo| + q|yo| + p|vo′| + q|uo′| + r|oo′|, p|xw| + q|uw| + q|yw′| + p|vw′| + l|ww′|.
In particular, for every τ > 0," the inequality (eq:Q) holds. The first statement is prop_crossing_first; for the second,
"add the two bounds and use rλ ≤ (τ/2)r² + λ²/(2τ)". -/
theorem prop_crossing {Y : Type} {d : Y → Y → ℝ} (hd : IsPrice K d) (x v y u o o' w w' : Y)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (∃ r l : ℝ, 0 ≤ r ∧ 0 ≤ l ∧ r ^ 2 + l ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) ∧
      p * d x v + q * d y u ≤ p * d x o + q * d y o + p * d v o' + q * d u o' + r * d o o' ∧
      p * d x v + q * d y u ≤ p * d x w + q * d u w + q * d y w' + p * d v w' + l * d w w') ∧
    ∀ τ : ℝ, 0 < τ → 2 * (p * d x v + q * d y u) ≤
      p * (d x o + d v o' + d x w + d v w') + q * (d y o + d u o' + d u w + d y w') +
        τ * (p ^ 2 + q ^ 2) + (d o o' ^ 2 + d w w' ^ 2) / (2 * τ) := by
  refine ⟨prop_crossing_first hd x v y u o o' w w' hp hq, fun τ hτ => ?_⟩
  obtain ⟨r, l, hr, hl, hrl, h1, h2⟩ := prop_crossing_first hd x v y u o o' w w' hp hq
  have am : ∀ a b : ℝ, a * b ≤ τ / 2 * a ^ 2 + b ^ 2 / (2 * τ) := by
    intro a b
    have e : τ / 2 * a ^ 2 + b ^ 2 / (2 * τ) - a * b = (τ * a - b) ^ 2 / (2 * τ) := by
      field_simp
      ring
    nlinarith [div_nonneg (sq_nonneg (τ * a - b)) (by positivity : (0 : ℝ) ≤ 2 * τ)]
  have a1 := am r (d o o')
  have a2 := am l (d w w')
  have a3 : τ / 2 * (r ^ 2 + l ^ 2) ≤ τ / 2 * (2 * (p ^ 2 + q ^ 2)) :=
    mul_le_mul_of_nonneg_left hrl (by positivity)
  rw [add_div]
  nlinarith

/-- **Paper: display eq:Q.** "In particular, for every τ > 0, 2(p|xv| + q|yu|) ≤ p(|xo| + |vo′| + |xw| + |vw′|) +
q(|yo| + |uo′| + |uw| + |yw′|) + τ(p² + q²) + (|oo′|² + |ww′|²)/(2τ)." This is the second statement of Proposition prop:crossing. -/
theorem eq_Q {Y : Type} {d : Y → Y → ℝ} (hd : IsPrice K d) (x v y u o o' w w' : Y)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (τ : ℝ) (hτ : 0 < τ) :
    2 * (p * d x v + q * d y u) ≤
      p * (d x o + d v o' + d x w + d v w') + q * (d y o + d u o' + d u w + d y w') +
        τ * (p ^ 2 + q ^ 2) + (d o o' ^ 2 + d w w' ^ 2) / (2 * τ) :=
  (prop_crossing hd x v y u o o' w w' hp hq).2 τ hτ

end Paper
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Complete CAT(0) spaces: definitions

`Cat.CN X`: `X` is complete and any two points have a midpoint with the CN inequality.
What follows from the defining inequalities of barycentres (`IsBary`) and of points at
fraction `t` (`IsPt`) in any metric space. The facts on CAT(0) spaces are Lemma lem:toolkit, in Paper/Toolkit.lean.
-/

open Filter Topology

namespace Cat

/-- Complete CAT(0) spaces: complete, and every two points have a midpoint with the
inequality of Bruhat and Tits. -/
class CN (X : Type*) [MetricSpace X] : Prop extends CompleteSpace X where
  exists_mid : ∀ x v : X, ∃ m : X, ∀ z : X,
    dist z m ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4

variable {X : Type*} [MetricSpace X]

section min
variable [CN X]

/-- The midpoint. -/
noncomputable def mid (x v : X) : X := Classical.choose (CN.exists_mid x v)

theorem cn (x v z : X) :
    dist z (mid x v) ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4 :=
  Classical.choose_spec (CN.exists_mid x v) z

theorem dist_mid_left (x v : X) : dist x (mid x v) = dist x v / 2 := by
  have h1 := cn x v x
  have h2 := cn x v v
  have h3 := dist_triangle x (mid x v) v
  rw [dist_self] at h1 h2
  rw [dist_comm v x] at h2
  rw [dist_comm (mid x v) v] at h3
  have ha : dist x (mid x v) ≤ dist x v / 2 := by
    apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
    nlinarith
  have hb : dist v (mid x v) ≤ dist x v / 2 := by
    apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
    nlinarith
  linarith

theorem dist_mid_right (x v : X) : dist (mid x v) v = dist x v / 2 := by
  have h2 := cn x v v
  have h3 := dist_triangle x (mid x v) v
  rw [dist_mid_left] at h3
  rw [dist_self, dist_comm v x] at h2
  rw [dist_comm (mid x v) v] at h3 ⊢
  have hb : dist v (mid x v) ≤ dist x v / 2 := by
    apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
    nlinarith
  linarith

end min

/-! ### Barycentres -/

section bary
variable {ι : Type*} [Fintype ι]

/-- `b` is the barycentre of the points `x i` with weights `w i` (of any total weight):
the inequality of variances. -/
def IsBary (w : ι → ℝ) (x : ι → X) (b : X) : Prop :=
  ∀ y, ∑ i, w i * dist b (x i) ^ 2 + (∑ i, w i) * dist y b ^ 2 ≤ ∑ i, w i * dist y (x i) ^ 2

theorem IsBary.unique {w : ι → ℝ} {x : ι → X} {b b' : X} (hw : 0 < ∑ i, w i)
    (h : IsBary w x b) (h' : IsBary w x b') : b = b' := by
  have h1 := h b'
  have h2 := h' b
  rw [dist_comm] at h1
  have h3 : (∑ i, w i) * dist b b' ^ 2 ≤ 0 := by linarith
  have h4 : dist b b' ^ 2 ≤ 0 := by
    by_contra h5
    push Not at h5
    exact absurd h3 (not_le.2 (mul_pos hw h5))
  have h5 : dist b b' = 0 := by
    have := sq_nonneg (dist b b')
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h4 this)
  exact dist_eq_zero.1 h5

/-- A barycentre is mapped to a barycentre by a surjective isometry. -/
theorem IsBary.map {Y : Type*} [MetricSpace Y] {w : ι → ℝ} {x : ι → X} {b : X}
    (h : IsBary w x b) {f : X → Y} (hf : Isometry f) (hs : Function.Surjective f) :
    IsBary w (fun i => f (x i)) (f b) := by
  intro y
  obtain ⟨y, rfl⟩ := hs y
  simpa only [hf.dist_eq] using h y

/-- Barycentres don't depend on the names of the points. -/
theorem IsBary.comp_equiv {κ : Type*} [Fintype κ] {w : ι → ℝ} {x : ι → X} {b : X}
    (h : IsBary w x b) (e : κ ≃ ι) : IsBary (w ∘ e) (x ∘ e) b := by
  intro y
  have h1 := h y
  rw [← e.sum_comp fun i => w i * dist b (x i) ^ 2, ← e.sum_comp w,
    ← e.sum_comp fun i => w i * dist y (x i) ^ 2] at h1
  exact h1

end bary

/-! ### Points at fraction `t` -/

/-- `b` is the point at fraction `t` between `x` and `v`. -/
def IsPt (x v : X) (t : ℝ) (b : X) : Prop :=
  ∀ z, dist z b ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z v ^ 2 - t * (1 - t) * dist x v ^ 2

theorem IsPt.dist_left {x v b : X} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (h : IsPt x v t b) :
    dist x b = t * dist x v := by
  have h2 := h x
  have h3 := h v
  have h4 := dist_triangle x b v
  rw [dist_self] at h2 h3
  rw [dist_comm v x] at h3
  rw [dist_comm b v] at h4
  have ha : dist x b ≤ t * dist x v := by
    apply abs_le_of_sq_le_sq' _ (mul_nonneg h0 dist_nonneg) |>.2
    nlinarith
  have hb : dist v b ≤ (1 - t) * dist x v := by
    apply abs_le_of_sq_le_sq' _ (mul_nonneg (by linarith) dist_nonneg) |>.2
    nlinarith
  linarith

theorem IsPt.symm {x v b : X} {t : ℝ} (h : IsPt x v t b) : IsPt v x (1 - t) b := by
  intro z
  have := h z
  rw [dist_comm v x]
  linarith

theorem IsPt.dist_right {x v b : X} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (h : IsPt x v t b) :
    dist b v = (1 - t) * dist x v := by
  have := h.symm.dist_left (by linarith) (by linarith)
  rw [dist_comm b v, this, dist_comm v x]

/-- A point with the distances of the point at fraction `t` is the point at fraction `t`. -/
theorem IsPt.eq_of_dist {x v b b' : X} {t : ℝ} (h : IsPt x v t b)
    (h2 : dist x b' = t * dist x v) (h3 : dist b' v = (1 - t) * dist x v) : b' = b := by
  have h4 := h b'
  rw [dist_comm b' x, h2, h3] at h4
  have h5 : dist b' b ^ 2 ≤ 0 := by nlinarith
  exact dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h5 (sq_nonneg _)))

theorem le_two_mul_of_forall {S a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ τ : ℝ, 0 < τ → S ≤ τ * b ^ 2 + a ^ 2 / τ) : S ≤ 2 * a * b := by
  rcases ha.eq_or_lt with rfl | ha
  · by_contra hS
    push Not at hS
    simp only [mul_zero, zero_mul] at hS
    have h1 := h (S / (2 * (b ^ 2 + 1))) (by positivity)
    have h2 : S / (2 * (b ^ 2 + 1)) * b ^ 2 ≤ S / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    simp at h1
    linarith
  rcases hb.eq_or_lt with rfl | hb
  · by_contra hS
    push Not at hS
    rw [mul_zero] at hS
    have h1 := h (2 * (a ^ 2 + 1) / S) (by positivity)
    have h2 : a ^ 2 / (2 * (a ^ 2 + 1) / S) ≤ S / 2 := by
      rw [div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h3 : 2 * (a ^ 2 + 1) / S * (0 : ℝ) ^ 2 = 0 := by ring
    linarith
  · have h1 := h (a / b) (by positivity)
    have h2 : a / b * b ^ 2 + a ^ 2 / (a / b) = 2 * a * b := by
      field_simp
      ring
    linarith

end Cat
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Means over large windows

Windows: two sheets (`Bool`), `0 ≤ i < n²`, `0 ≤ k < n`. `mean f` is the limit (along an
ultrafilter) of the means of `f n` over the `n`-th window: a positive linear functional on bounded
functions, invariant under translations, with the inequality of Cauchy and Schwarz.
-/

open Filter Topology Finset

namespace Cat

/-- Functions on two sheets of `ℤ²`, one for every `n`. -/
abbrev Fn := ℕ → Bool → ℤ → ℤ → ℝ

/-- The mean over the `n`-th window. -/
noncomputable def avg (n : ℕ) (f : Bool → ℤ → ℤ → ℝ) : ℝ :=
  (∑ b, ∑ i ∈ range (n ^ 2), ∑ k ∈ range n, f b i k) / (2 * n ^ 3)

/-- Bounded functions. -/
def Bd (f : Fn) : Prop := ∃ C, ∀ n b i k, |f n b i k| ≤ C

theorem Bd.add {f g : Fn} (hf : Bd f) (hg : Bd g) : Bd (f + g) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  exact ⟨C + D, fun n b i k => (abs_add_le _ _).trans (add_le_add (hC n b i k) (hD n b i k))⟩

theorem Bd.mul {f g : Fn} (hf : Bd f) (hg : Bd g) : Bd (f * g) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C * D, fun n b i k => ?_⟩
  simp only [Pi.mul_apply, abs_mul]
  exact mul_le_mul (hC n b i k) (hD n b i k) (abs_nonneg _) ((abs_nonneg _).trans (hC n b i k))

theorem Bd.smul {f : Fn} (hf : Bd f) (c : ℝ) : Bd (c • f) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨|c| * C, fun n b i k => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC n b i k) (abs_nonneg _)

theorem Bd.const (c : ℝ) : Bd fun _ _ _ _ => c := ⟨|c|, fun _ _ _ _ => le_rfl⟩

theorem Bd.shift {f : Fn} (hf : Bd f) (a c : ℤ) : Bd fun n b i k => f n b (i + a) (k + c) := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun n b i k => hC _ _ _ _⟩

theorem avg_add (n : ℕ) (f g : Bool → ℤ → ℤ → ℝ) : avg n (f + g) = avg n f + avg n g := by
  simp only [avg, Pi.add_apply, Finset.sum_add_distrib, add_div]

theorem avg_smul (n : ℕ) (c : ℝ) (f : Bool → ℤ → ℤ → ℝ) : avg n (c • f) = c * avg n f := by
  simp only [avg, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc]

theorem avg_mono {n : ℕ} {f g : Bool → ℤ → ℤ → ℝ}
    (h : ∀ b, ∀ i < n ^ 2, ∀ k < n, f b (i : ℕ) (k : ℕ) ≤ g b (i : ℕ) (k : ℕ)) :
    avg n f ≤ avg n g := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun k hk =>
    h b i (Finset.mem_range.1 hi) k (Finset.mem_range.1 hk)

theorem avg_const {n : ℕ} (hn : n ≠ 0) (c : ℝ) : avg n (fun _ _ _ => c) = c := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [avg, Finset.sum_const, Finset.card_univ, Fintype.card_bool, Finset.card_range,
    nsmul_eq_mul]
  push_cast
  field_simp

theorem abs_avg_le {n : ℕ} {f : Bool → ℤ → ℤ → ℝ} {C : ℝ} (h : ∀ b i k, |f b i k| ≤ C) :
    |avg n f| ≤ C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (h true 0 0)
  rcases eq_or_ne n 0 with rfl | hn
  · simpa [avg] using hC
  · rw [abs_le]
    constructor
    · calc -C = avg n (fun _ _ _ => -C) := (avg_const hn _).symm
        _ ≤ _ := avg_mono fun b i _ k _ => (abs_le.1 (h b i k)).1
    · calc avg n f ≤ avg n (fun _ _ _ => C) := avg_mono fun b i _ k _ => (abs_le.1 (h b i k)).2
        _ = C := avg_const hn _

/-- The mean of a bounded function over large windows. -/
noncomputable def mean (f : Fn) : ℝ := limUnder (hyperfilter ℕ : Filter ℕ) fun n => avg n (f n)

theorem tendsto_mean {f : Fn} (hf : Bd f) :
    Tendsto (fun n => avg n (f n)) (hyperfilter ℕ : Filter ℕ) (𝓝 (mean f)) := by
  obtain ⟨C, hC⟩ := hf
  have h1 : ∀ n, avg n (f n) ∈ Set.Icc (-C) C := fun n => abs_le.1 (abs_avg_le (hC n))
  obtain ⟨a, -, ha⟩ := (isCompact_Icc (a := -C) (b := C)).ultrafilter_le_nhds
    ((hyperfilter ℕ).map fun n => avg n (f n)) (by
      rw [le_principal_iff]
      exact Filter.mem_map.2 (Filter.univ_mem' h1))
  exact tendsto_nhds_limUnder ⟨a, ha⟩

theorem mean_eq {f : Fn} (hf : Bd f) {c : ℝ}
    (h : Tendsto (fun n => avg n (f n)) atTop (𝓝 c)) : mean f = c :=
  tendsto_nhds_unique (tendsto_mean hf) (h.mono_left Nat.hyperfilter_le_atTop)

theorem mean_add {f g : Fn} (hf : Bd f) (hg : Bd g) : mean (f + g) = mean f + mean g := by
  refine tendsto_nhds_unique (tendsto_mean (hf.add hg)) ?_
  have := (tendsto_mean hf).add (tendsto_mean hg)
  simpa only [Pi.add_apply, avg_add] using this

theorem mean_smul {f : Fn} (hf : Bd f) (c : ℝ) : mean (c • f) = c * mean f := by
  refine tendsto_nhds_unique (tendsto_mean (hf.smul c)) ?_
  have := (tendsto_mean hf).const_mul c
  simpa only [Pi.smul_apply, avg_smul] using this

theorem mean_const (c : ℝ) : mean (fun _ _ _ _ => c) = c := by
  refine mean_eq (Bd.const c) ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (avg_const hn c).symm

theorem mean_mono {f g : Fn} (hf : Bd f) (hg : Bd g)
    (h : ∀ᶠ n : ℕ in atTop, ∀ b, ∀ i < n ^ 2, ∀ k < n,
      f n b (i : ℕ) (k : ℕ) ≤ g n b (i : ℕ) (k : ℕ)) : mean f ≤ mean g := by
  refine le_of_tendsto_of_tendsto (tendsto_mean hf) (tendsto_mean hg) ?_
  exact (h.filter_mono Nat.hyperfilter_le_atTop).mono fun n hn => avg_mono hn

theorem mean_nonneg {f : Fn} (hf : Bd f) (h : ∀ n b i k, 0 ≤ f n b i k) : 0 ≤ mean f := by
  rw [← mean_const 0]
  exact mean_mono (Bd.const 0) hf (Eventually.of_forall fun _ _ _ _ _ _ => h _ _ _ _)

theorem mean_le {f g : Fn} (hf : Bd f) (hg : Bd g) (h : ∀ n b i k, f n b i k ≤ g n b i k) :
    mean f ≤ mean g :=
  mean_mono hf hg (Eventually.of_forall fun _ _ _ _ _ _ => h _ _ _ _)

/-! ### Translations -/

theorem sum_shift (φ : ℤ → ℝ) (N : ℕ) :
    ∑ i ∈ range N, φ ((i : ℤ) + 1) = ∑ i ∈ range N, φ (i : ℤ) + (φ N - φ 0) := by
  have h := Finset.sum_range_sub (fun i : ℕ => φ (i : ℤ)) N
  rw [Finset.sum_sub_distrib] at h
  push_cast at h
  linarith

theorem mean_eq_of_sub {f g : Fn} (hf : Bd f) (hg : Bd g)
    (h : Tendsto (fun n => avg n (f n) - avg n (g n)) atTop (𝓝 0)) : mean f = mean g := by
  have h1 := (tendsto_mean hf).sub (tendsto_mean hg)
  have h2 := tendsto_nhds_unique h1 (h.mono_left Nat.hyperfilter_le_atTop)
  linarith

theorem mean_shift_one {f : Fn} (hf : Bd f) :
    mean (fun n b i k => f n b (i + 1) k) = mean f := by
  obtain ⟨C, hC⟩ := id hf
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 true 0 0)
  refine mean_eq_of_sub (by simpa using hf.shift 1 0) hf ?_
  refine squeeze_zero_norm' (a := fun n : ℕ => 2 * C * (1 / (n : ℝ))) ?_ ?_
  · filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h1 : (avg n fun b i k => f n b (i + 1) k) - avg n (f n) =
        (∑ b, ∑ k ∈ range n, (f n b ((n ^ 2 : ℕ) : ℤ) k - f n b 0 k)) / (2 * n ^ 3) := by
      rw [avg, avg, ← sub_div, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm, Finset.sum_comm (s := range (n ^ 2)), ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sum_shift (fun i => f n b i k)]
      ring
    rw [h1, Real.norm_eq_abs, abs_div, abs_of_pos (show (0 : ℝ) < 2 * n ^ 3 by positivity),
      div_le_iff₀ (by positivity)]
    have h2 : |∑ b, ∑ k ∈ range n, (f n b ((n ^ 2 : ℕ) : ℤ) k - f n b 0 k)| ≤
        ∑ b : Bool, ∑ k ∈ range n, 2 * C := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      refine (abs_sub _ _).trans ?_
      linarith [hC n b ((n ^ 2 : ℕ) : ℤ) k, hC n b 0 k]
    refine h2.trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Finset.card_range,
      nsmul_eq_mul]
    have h3 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h4 : 2 * C * (1 / (n : ℝ)) * (2 * n ^ 3) = 4 * C * n ^ 2 := by field_simp; ring
    rw [h4]
    push_cast
    nlinarith [mul_nonneg hC0 hn'.le]
  · simpa using tendsto_one_div_atTop_nhds_zero_nat.const_mul (2 * C)

theorem mean_shift_one' {f : Fn} (hf : Bd f) :
    mean (fun n b i k => f n b i (k + 1)) = mean f := by
  obtain ⟨C, hC⟩ := id hf
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 true 0 0)
  refine mean_eq_of_sub (by simpa using hf.shift 0 1) hf ?_
  refine squeeze_zero_norm' (a := fun n : ℕ => 2 * C * (1 / (n : ℝ))) ?_ ?_
  · filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h1 : (avg n fun b i k => f n b i (k + 1)) - avg n (f n) =
        (∑ b, ∑ i ∈ range (n ^ 2), (f n b i (n : ℕ) - f n b i 0)) / (2 * n ^ 3) := by
      rw [avg, avg, ← sub_div, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sum_shift (fun k => f n b i k)]
      ring
    rw [h1, Real.norm_eq_abs, abs_div, abs_of_pos (show (0 : ℝ) < 2 * n ^ 3 by positivity),
      div_le_iff₀ (by positivity)]
    have h2 : |∑ b, ∑ i ∈ range (n ^ 2), (f n b i (n : ℕ) - f n b i 0)| ≤
        ∑ b : Bool, ∑ k ∈ range (n ^ 2), 2 * C := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (abs_sub _ _).trans ?_
      linarith [hC n b i (n : ℕ), hC n b i 0]
    refine h2.trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Finset.card_range,
      nsmul_eq_mul]
    have h4 : 2 * C * (1 / (n : ℝ)) * (2 * n ^ 3) = 4 * C * n ^ 2 := by field_simp; ring
    rw [h4]
    push_cast
    nlinarith
  · simpa using tendsto_one_div_atTop_nhds_zero_nat.const_mul (2 * C)

theorem mean_shift_left {f : Fn} (hf : Bd f) (a : ℤ) :
    mean (fun n b i k => f n b (i + a) k) = mean f := by
  induction a using Int.induction_on with
  | zero => simp
  | succ a ih =>
    rw [← ih, ← mean_shift_one (f := fun n b i k => f n b (i + a) k) (by simpa using hf.shift a 0)]
    congr 1
    funext n b i k
    congr 1
    ring
  | pred a ih =>
    rw [← ih, ← mean_shift_one (f := fun n b i k => f n b (i + (-a - 1)) k)
      (by simpa using hf.shift (-a - 1) 0)]
    congr 1
    funext n b i k
    congr 1
    ring

theorem mean_shift_right {f : Fn} (hf : Bd f) (a : ℤ) :
    mean (fun n b i k => f n b i (k + a)) = mean f := by
  induction a using Int.induction_on with
  | zero => simp
  | succ a ih =>
    rw [← ih, ← mean_shift_one' (f := fun n b i k => f n b i (k + a))
      (by simpa using hf.shift 0 a)]
    congr 1
    funext n b i k
    congr 1
    ring
  | pred a ih =>
    rw [← ih, ← mean_shift_one' (f := fun n b i k => f n b i (k + (-a - 1)))
      (by simpa using hf.shift 0 (-a - 1))]
    congr 1
    funext n b i k
    congr 1
    ring

theorem mean_shift {f : Fn} (hf : Bd f) (a c : ℤ) :
    mean (fun n b i k => f n b (i + a) (k + c)) = mean f := by
  rw [mean_shift_left (f := fun n b i k => f n b i (k + c)) (by simpa using hf.shift 0 c) a,
    mean_shift_right hf c]

/-- A telescoping sum. -/
theorem le_mean_tele {F : Fn} (hX : Bd fun n b i k => (n : ℝ) ^ 2 * (F n b (i + 1) k - F n b i k))
    {c : ℕ → ℝ} {c₀ : ℝ} (hc : Tendsto c atTop (𝓝 c₀))
    (h : ∀ᶠ n : ℕ in atTop, ∀ k < n,
      c n ≤ ∑ b, (F n b ((n ^ 2 : ℕ) : ℤ) (k : ℕ) - F n b 0 (k : ℕ))) :
    c₀ / 2 ≤ mean fun n b i k => (n : ℝ) ^ 2 * (F n b (i + 1) k - F n b i k) := by
  refine le_of_tendsto_of_tendsto ((hc.div_const 2).mono_left Nat.hyperfilter_le_atTop)
    (tendsto_mean hX) ?_
  refine Filter.Eventually.filter_mono Nat.hyperfilter_le_atTop ?_
  filter_upwards [h, eventually_ne_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have h1 : (avg n fun b i k => (n : ℝ) ^ 2 * (F n b (i + 1) k - F n b i k)) =
      (∑ k ∈ range n, ∑ b, (F n b ((n ^ 2 : ℕ) : ℤ) k - F n b 0 k)) / (2 * n) := by
    rw [avg, Finset.sum_comm (s := range n)]
    have : ∀ b : Bool, ∑ i ∈ range (n ^ 2), ∑ k ∈ range n,
        (n : ℝ) ^ 2 * (F n b ((i : ℤ) + 1) k - F n b i k) =
        (n : ℝ) ^ 2 * ∑ k ∈ range n, (F n b ((n ^ 2 : ℕ) : ℤ) k - F n b 0 k) := by
      intro b
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_shift (fun i => F n b i k)]
      ring
    rw [Finset.sum_congr rfl fun b _ => this b, ← Finset.mul_sum]
    field_simp
  rw [h1, div_le_div_iff₀ (by norm_num) (by positivity)]
  have h2 : ∑ k ∈ range n, c n ≤
      ∑ k ∈ range n, ∑ b, (F n b ((n ^ 2 : ℕ) : ℤ) k - F n b 0 k) :=
    Finset.sum_le_sum fun k hk => hn k (Finset.mem_range.1 hk)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  linarith

/-- Many steps of a telescoping sum. -/
theorem mean_steps {F : Fn} (hX : Bd fun n b i k => (n : ℝ) ^ 2 * (F n b (i + 1) k - F n b i k))
    (S : ℕ) : Bd (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + S) k - F n b i k)) ∧
      mean (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + S) k - F n b i k)) =
        S * mean fun n b i k => (n : ℝ) ^ 2 * (F n b (i + 1) k - F n b i k) := by
  induction S with
  | zero =>
    have : (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + (0 : ℕ)) k - F n b i k) : Fn) =
        fun _ _ _ _ => (0 : ℝ) := by
      funext n b i k
      simp
    rw [this, mean_const, Nat.cast_zero, zero_mul]
    exact ⟨Bd.const 0, rfl⟩
  | succ S ih =>
    have hs := hX.shift S 0
    simp only [add_zero] at hs
    have : (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + (S + 1 : ℕ)) k - F n b i k) : Fn) =
        (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + S + 1) k - F n b (i + S) k) : Fn) +
          (fun n b i k => (n : ℝ) ^ 2 * (F n b (i + S) k - F n b i k) : Fn) := by
      funext n b i k
      simp only [Pi.add_apply]
      push_cast
      rw [← add_assoc i]
      ring
    rw [this]
    refine ⟨hs.add ih.1, ?_⟩
    rw [mean_add hs ih.1, ih.2]
    rw [mean_shift_left hX S]
    push_cast
    ring

/-! ### Cauchy and Schwarz -/

/-- The root of the mean square. -/
noncomputable def nm (f : Fn) : ℝ := √(mean (f * f))

theorem nm_nonneg (f : Fn) : 0 ≤ nm f := Real.sqrt_nonneg _

theorem nm_sq {f : Fn} (hf : Bd f) : nm f ^ 2 = mean (f * f) :=
  Real.sq_sqrt (mean_nonneg (hf.mul hf) fun _ _ _ _ => mul_self_nonneg _)

theorem mean_mul_le {f g : Fn} (hf : Bd f) (hg : Bd g) : mean (f * g) ≤ nm f * nm g := by
  have h : 2 * mean (f * g) ≤ 2 * nm g * nm f := by
    apply le_two_mul_of_forall (nm_nonneg g) (nm_nonneg f)
    intro τ hτ
    rw [nm_sq hf, nm_sq hg]
    have h1 : mean ((2 : ℝ) • (f * g)) ≤ mean (τ • (f * f) + τ⁻¹ • (g * g)) := by
      apply mean_le ((hf.mul hg).smul 2) (((hf.mul hf).smul τ).add ((hg.mul hg).smul τ⁻¹))
      intro n b i k
      simp only [Pi.smul_apply, Pi.mul_apply, Pi.add_apply, smul_eq_mul]
      have h2 : 0 ≤ τ⁻¹ * (τ * f n b i k - g n b i k) ^ 2 :=
        mul_nonneg (inv_nonneg.2 hτ.le) (sq_nonneg _)
      have h3 : τ⁻¹ * (τ * f n b i k - g n b i k) ^ 2 =
          τ * (f n b i k * f n b i k) + τ⁻¹ * (g n b i k * g n b i k)
            - 2 * (f n b i k * g n b i k) := by field_simp; ring
      linarith
    rw [mean_smul (hf.mul hg), mean_add ((hf.mul hf).smul τ) ((hg.mul hg).smul τ⁻¹),
      mean_smul (hf.mul hf), mean_smul (hg.mul hg)] at h1
    rw [div_eq_inv_mul]
    exact h1
  linarith

theorem nm_mono {f g : Fn} (hf : Bd f) (hg : Bd g) (h0 : ∀ n b i k, 0 ≤ f n b i k)
    (h : ∀ᶠ n : ℕ in atTop, ∀ b, ∀ i < n ^ 2, ∀ k < n,
      f n b (i : ℕ) (k : ℕ) ≤ g n b (i : ℕ) (k : ℕ)) : nm f ≤ nm g := by
  apply Real.sqrt_le_sqrt
  apply mean_mono (hf.mul hf) (hg.mul hg)
  filter_upwards [h] with n hn b i hi k hk
  exact mul_self_le_mul_self (h0 _ _ _ _) (hn b i hi k hk)

theorem nm_add_le {f g : Fn} (hf : Bd f) (hg : Bd g) : nm (f + g) ≤ nm f + nm g := by
  apply abs_le_of_sq_le_sq' _ (add_nonneg (nm_nonneg f) (nm_nonneg g)) |>.2
  rw [nm_sq (hf.add hg), add_sq, nm_sq hf, nm_sq hg]
  have h1 : (f + g) * (f + g) = f * f + (2 : ℝ) • (f * g) + g * g := by
    funext n b i k
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1, mean_add ((hf.mul hf).add ((hf.mul hg).smul 2)) (hg.mul hg),
    mean_add (hf.mul hf) ((hf.mul hg).smul 2), mean_smul (hf.mul hg)]
  linarith [mean_mul_le hf hg]

theorem mean_le_nm {f : Fn} (hf : Bd f) : mean f ≤ nm f := by
  have h := mean_mul_le hf (Bd.const 1)
  have h1 : f * (fun _ _ _ _ => (1 : ℝ)) = f := by
    funext n b i k
    simp
  have h2 : nm (fun _ _ _ _ => (1 : ℝ)) = 1 := by
    have : ((fun _ _ _ _ => (1 : ℝ)) * (fun _ _ _ _ => (1 : ℝ)) : Fn) = fun _ _ _ _ => 1 := by
      funext n b i k
      simp
    rw [nm, this, mean_const, Real.sqrt_one]
  rw [h1, h2, mul_one] at h
  exact h

theorem nm_shift {f : Fn} (hf : Bd f) (a c : ℤ) :
    nm (fun n b i k => f n b (i + a) (k + c)) = nm f := by
  rw [nm, nm, ← mean_shift (hf.mul hf) a c]
  rfl

end Cat
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Length functions on `ℤ²` with the crossing inequality

`Len N`: an even subadditive function on `ℤ²` with the inequality (Q). Its homogeneous version
satisfies (Q), too. (That a homogeneous one satisfies the law of the parallelogram is Lemma lem:means, in Paper/Means.lean.)
-/

open Filter Topology Finset

namespace Cat

/-- Even subadditive functions on `ℤ²` with the inequality (Q). -/
structure Len (N : ℤ × ℤ → ℝ) : Prop where
  nonneg : ∀ h, 0 ≤ N h
  zero : N 0 = 0
  neg : ∀ h, N (-h) = N h
  add : ∀ h h', N (h + h') ≤ N h + N h'
  q : ∀ X V Y U n n' k k' : ℤ × ℤ, ∀ τ : ℝ, 0 < τ →
    2 * (N (X - V) ^ 2 + N (Y - U) ^ 2) ≤
      N (X - V) * (N (X - n) + N (V - n') + N (X - k) + N (V - k'))
      + N (Y - U) * (N (Y - n) + N (U - n') + N (U - k) + N (Y - k'))
      + τ * (N (X - V) ^ 2 + N (Y - U) ^ 2) + (N (n - n') ^ 2 + N (k - k') ^ 2) / (2 * τ)

/-- Homogeneous along natural numbers. -/
def Homog (N : ℤ × ℤ → ℝ) : Prop := ∀ (m : ℕ) h, N (m • h) = m * N h

theorem Len.subadditive {N : ℤ × ℤ → ℝ} (hN : Len N) (h : ℤ × ℤ) :
    Subadditive fun S : ℕ => N (S • h) := by
  intro m n
  simp only [add_smul]
  exact hN.add _ _

/-- The homogeneous version of a length function. -/
theorem Len.exists_homog {N : ℤ × ℤ → ℝ} (hN : Len N) :
    ∃ N' : ℤ × ℤ → ℝ, Len N' ∧ Homog N' ∧ (∀ h, N' h ≤ N h) ∧
      ∀ h (c : ℝ), (∀ S : ℕ, 0 < S → c * S ≤ N (S • h)) → c ≤ N' h := by
  let N' : ℤ × ℤ → ℝ := fun h => (hN.subadditive h).lim
  have hbdd : ∀ h, BddBelow (Set.range fun S : ℕ => N (S • h) / S) := by
    intro h
    refine ⟨0, ?_⟩
    rintro _ ⟨S, rfl⟩
    exact div_nonneg (hN.nonneg _) (Nat.cast_nonneg _)
  have hT : ∀ h, Tendsto (fun S : ℕ => N (S • h) / S) atTop (𝓝 (N' h)) := fun h =>
    (hN.subadditive h).tendsto_lim (hbdd h)
  have hhom : Homog N' := by
    intro m h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h1 := hT ((0 : ℕ) • h)
      simp only [zero_smul, smul_zero, hN.zero, zero_div] at h1
      rw [Nat.cast_zero, zero_mul, zero_smul]
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    · have h1 := hT (m • h)
      have h2 : Tendsto (fun S : ℕ => (m : ℝ) * (N ((S * m) • h) / (S * m : ℕ))) atTop
          (𝓝 (m * N' h)) :=
        ((hT h).comp (tendsto_id.atTop_mul_const' hm)).const_mul _
      refine tendsto_nhds_unique h1 (h2.congr fun S => ?_)
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      rw [mul_smul]
      push_cast
      rcases Nat.eq_zero_or_pos S with rfl | hS
      · simp
      · have hS' : (S : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
        field_simp
  refine ⟨N', ⟨?_, ?_, ?_, ?_, ?_⟩, hhom, ?_, ?_⟩
  · exact fun h => ge_of_tendsto' (hT h) fun S => div_nonneg (hN.nonneg _) (Nat.cast_nonneg _)
  · have := hhom 0 0
    simpa using this
  · intro h
    refine tendsto_nhds_unique (hT (-h)) ((hT h).congr fun S => ?_)
    rw [smul_neg, hN.neg]
  · intro h h'
    refine le_of_tendsto_of_tendsto' (hT _) ((hT h).add (hT h')) fun S => ?_
    rw [smul_add, ← add_div]
    exact div_le_div_of_nonneg_right (hN.add _ _) (Nat.cast_nonneg _)
  · intro X V Y U n n' k k' τ hτ
    have hl : Tendsto (fun S : ℕ => 2 * ((N (S • (X - V)) / S) ^ 2 + (N (S • (Y - U)) / S) ^ 2))
        atTop (𝓝 (2 * (N' (X - V) ^ 2 + N' (Y - U) ^ 2))) :=
      (((hT _).pow 2).add ((hT _).pow 2)).const_mul 2
    have hr : Tendsto (fun S : ℕ =>
        N (S • (X - V)) / S * (N (S • (X - n)) / S + N (S • (V - n')) / S
          + N (S • (X - k)) / S + N (S • (V - k')) / S)
        + N (S • (Y - U)) / S * (N (S • (Y - n)) / S + N (S • (U - n')) / S
          + N (S • (U - k)) / S + N (S • (Y - k')) / S)
        + τ * ((N (S • (X - V)) / S) ^ 2 + (N (S • (Y - U)) / S) ^ 2)
        + ((N (S • (n - n')) / S) ^ 2 + (N (S • (k - k')) / S) ^ 2) / (2 * τ)) atTop
        (𝓝 (N' (X - V) * (N' (X - n) + N' (V - n') + N' (X - k) + N' (V - k'))
          + N' (Y - U) * (N' (Y - n) + N' (U - n') + N' (U - k) + N' (Y - k'))
          + τ * (N' (X - V) ^ 2 + N' (Y - U) ^ 2)
          + (N' (n - n') ^ 2 + N' (k - k') ^ 2) / (2 * τ))) :=
      (((((hT _).mul ((((hT _).add (hT _)).add (hT _)).add (hT _)))).add
        ((hT _).mul ((((hT _).add (hT _)).add (hT _)).add (hT _)))).add
        ((((hT _).pow 2).add ((hT _).pow 2)).const_mul τ)).add
        ((((hT _).pow 2).add ((hT _).pow 2)).div_const _)
    refine le_of_tendsto_of_tendsto' hl hr fun S => ?_
    have h := hN.q (S • X) (S • V) (S • Y) (S • U) (S • n) (S • n') (S • k) (S • k') τ hτ
    simp only [← smul_sub] at h
    rcases Nat.eq_zero_or_pos S with rfl | hS
    · simp
    · have hS' : (0 : ℝ) < S := by exact_mod_cast hS
      have h2 := div_le_div_of_nonneg_right h (show 0 ≤ (S : ℝ) ^ 2 by positivity)
      refine le_trans (le_of_eq ?_) (h2.trans (le_of_eq ?_))
      · field_simp
      · field_simp
  · exact fun h => by
      have := (hN.subadditive h).lim_le_div (hbdd h) (n := 1) one_ne_zero
      simpa using this
  · intro h c hc
    refine ge_of_tendsto (hT h) ?_
    filter_upwards [eventually_gt_atTop 0] with S hS
    rw [le_div_iff₀ (by exact_mod_cast hS)]
    exact hc S hS

section par

variable {N : ℤ × ℤ → ℝ} (hN : Len N)

include hN in
theorem Len.sub_le (h h' : ℤ × ℤ) : N (h - h') ≤ N h + N h' := by
  rw [sub_eq_add_neg]
  exact (hN.add _ _).trans_eq (by rw [hN.neg])

include hN in
theorem Len.le_add_sub (h h' : ℤ × ℤ) : N h ≤ N (h - h') + N h' := by
  have := hN.add (h - h') h'
  rwa [sub_add_cancel] at this

include hN in
theorem Len.abs_sub_le (h h' : ℤ × ℤ) : |N h - N h'| ≤ N (h - h') := by
  rw [abs_le]
  constructor
  · have := hN.le_add_sub h' h
    rw [← hN.neg (h' - h), neg_sub] at this
    linarith
  · linarith [hN.le_add_sub h h']

end par

end Cat
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Mean squares of prices on `ℤ²` give a length function with the crossing inequality
-/

open Filter Topology Finset

namespace Cat

/-- For every `n` and every sheet a pseudometric on `ℤ²`, Lipschitz with one constant, with the
inequality (Q). -/
structure Lip (W : ℕ → Bool → ℤ × ℤ → ℤ × ℤ → ℝ) (Λ : ℝ) : Prop where
  nonneg : ∀ n b P P', 0 ≤ W n b P P'
  self : ∀ n b P, W n b P P = 0
  symm : ∀ n b P P', W n b P P' = W n b P' P
  tri : ∀ n b P P' P'', W n b P P'' ≤ W n b P P' + W n b P' P''
  lip : ∀ n b (P h : ℤ × ℤ), W n b P (P + h) ≤ Λ * (|(h.1 : ℝ)| + |(h.2 : ℝ)|)
  q : ∀ n b (X V Y U m m' k k' : ℤ × ℤ) (p q τ : ℝ), 0 ≤ p → 0 ≤ q → 0 < τ →
    2 * (p * W n b X V + q * W n b Y U) ≤
      p * (W n b X m + W n b V m' + W n b X k + W n b V k')
      + q * (W n b Y m + W n b U m' + W n b U k + W n b Y k')
      + τ * (p ^ 2 + q ^ 2) + (W n b m m' ^ 2 + W n b k k' ^ 2) / (2 * τ)

variable {W : ℕ → Bool → ℤ × ℤ → ℤ × ℤ → ℝ} {Λ : ℝ}

/-- The distance of two translates of the base point. -/
def df (W : ℕ → Bool → ℤ × ℤ → ℤ × ℤ → ℝ) (u v : ℤ × ℤ) : Fn :=
  fun n b i k => W n b ((i, k) + u) ((i, k) + v)

/-- The root mean square of the distances of `P` and `P+h`. -/
noncomputable def len (W : ℕ → Bool → ℤ × ℤ → ℤ × ℤ → ℝ) (h : ℤ × ℤ) : ℝ := nm (df W 0 h)

namespace Lip

variable (H : Lip W Λ)
include H

theorem bd (u v : ℤ × ℤ) : Bd (df W u v) := by
  refine ⟨Λ * (|((v - u).1 : ℝ)| + |((v - u).2 : ℝ)|), fun n b i k => ?_⟩
  rw [df, abs_of_nonneg (H.nonneg _ _ _ _)]
  have := H.lip n b ((i, k) + u) (v - u)
  rwa [add_assoc, add_sub_cancel] at this

theorem nm_df (u v : ℤ × ℤ) : nm (df W u v) = len W (u - v) := by
  have h1 : df W u v = df W v u := by
    funext n b i k
    exact H.symm _ _ _ _
  have h2 : df W v u = fun n b i k => df W 0 (u - v) n b (i + v.1) (k + v.2) := by
    funext n b i k
    simp only [df, add_zero]
    congr 1
    · ext <;> simp
  rw [h1, h2, nm_shift (H.bd _ _)]
  rfl

theorem nm_df' (u v : ℤ × ℤ) : nm (df W u v) = len W (v - u) := by
  rw [← H.nm_df v u]
  congr 1
  funext n b i k
  exact H.symm _ _ _ _

theorem len_zero : len W 0 = 0 := by
  have : df W 0 0 * df W 0 0 = fun _ _ _ _ => (0 : ℝ) := by
    funext n b i k
    simp [df, H.self]
  rw [len, nm, this, mean_const, Real.sqrt_zero]

/-- By translation invariance the root mean square is even. -/
theorem len_neg (h : ℤ × ℤ) : len W (-h) = len W h := by
  have := H.nm_df 0 h
  rw [zero_sub] at this
  exact this.symm

/-- By translation invariance and Minkowski's inequality the root mean square is subadditive. -/
theorem len_add (h h' : ℤ × ℤ) : len W (h + h') ≤ len W h + len W h' := by
  have h1 : nm (df W 0 (h + h')) ≤ nm (df W 0 h + df W h (h + h')) :=
    nm_mono (H.bd _ _) ((H.bd _ _).add (H.bd _ _)) (fun n b i k => H.nonneg _ _ _ _)
      (Eventually.of_forall fun n b i _ k _ => H.tri _ _ _ _ _)
  have h2 := nm_add_le (H.bd 0 h) (H.bd h (h + h'))
  rw [H.nm_df' h, add_sub_cancel_left] at h2
  exact h1.trans h2

/-- By the inequality of Cauchy and Schwarz the root mean square satisfies (Q), with the norms of differences for the
distances. -/
theorem len_q (X V Y U m m' k k' : ℤ × ℤ) (τ : ℝ) (hτ : 0 < τ) :
    2 * (len W (X - V) ^ 2 + len W (Y - U) ^ 2) ≤
      len W (X - V) * (len W (X - m) + len W (V - m') + len W (X - k) + len W (V - k'))
      + len W (Y - U) * (len W (Y - m) + len W (U - m') + len W (U - k) + len W (Y - k'))
      + τ * (len W (X - V) ^ 2 + len W (Y - U) ^ 2)
      + (len W (m - m') ^ 2 + len W (k - k') ^ 2) / (2 * τ) := by
  have hb := H.bd
  have key : mean ((2 : ℝ) • (df W X V * df W X V + df W Y U * df W Y U)) ≤
      mean (df W X V * df W X m + df W X V * df W V m' + df W X V * df W X k
        + df W X V * df W V k' + (df W Y U * df W Y m + df W Y U * df W U m'
        + df W Y U * df W U k + df W Y U * df W Y k')
        + τ • (df W X V * df W X V + df W Y U * df W Y U)
        + (1 / (2 * τ)) • (df W m m' * df W m m' + df W k k' * df W k k')) := by
    apply mean_le
    · repeat' first | exact hb _ _ | apply Bd.smul | apply Bd.add | apply Bd.mul
    · repeat' first | exact hb _ _ | apply Bd.smul | apply Bd.add | apply Bd.mul
    intro n b i j
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    have h := H.q n b ((i, j) + X) ((i, j) + V) ((i, j) + Y) ((i, j) + U) ((i, j) + m)
      ((i, j) + m') ((i, j) + k) ((i, j) + k') _ _ τ (H.nonneg n b ((i, j) + X) ((i, j) + V))
      (H.nonneg n b ((i, j) + Y) ((i, j) + U)) hτ
    simp only [df]
    rw [one_div, inv_mul_eq_div]
    simp only [pow_two] at h
    linarith
  have e1 : mean ((2 : ℝ) • (df W X V * df W X V + df W Y U * df W Y U)) =
      2 * (len W (X - V) ^ 2 + len W (Y - U) ^ 2) := by
    rw [mean_smul, mean_add, ← nm_sq (hb _ _), ← nm_sq (hb _ _), H.nm_df, H.nm_df]
    all_goals repeat' first | exact hb _ _ | apply Bd.smul | apply Bd.add | apply Bd.mul
  rw [e1] at key
  have e2 : mean (df W X V * df W X m + df W X V * df W V m' + df W X V * df W X k
        + df W X V * df W V k' + (df W Y U * df W Y m + df W Y U * df W U m'
        + df W Y U * df W U k + df W Y U * df W Y k')
        + τ • (df W X V * df W X V + df W Y U * df W Y U)
        + (1 / (2 * τ)) • (df W m m' * df W m m' + df W k k' * df W k k')) =
      mean (df W X V * df W X m) + mean (df W X V * df W V m') + mean (df W X V * df W X k)
        + mean (df W X V * df W V k') + (mean (df W Y U * df W Y m) + mean (df W Y U * df W U m')
        + mean (df W Y U * df W U k) + mean (df W Y U * df W Y k'))
        + τ * (len W (X - V) ^ 2 + len W (Y - U) ^ 2)
        + 1 / (2 * τ) * (len W (m - m') ^ 2 + len W (k - k') ^ 2) := by
    rw [mean_add, mean_add, mean_add, mean_add, mean_add, mean_add, mean_add, mean_add,
      mean_add, mean_smul, mean_smul, mean_add, mean_add, ← nm_sq (hb _ _), ← nm_sq (hb _ _),
      ← nm_sq (hb _ _), ← nm_sq (hb _ _), H.nm_df, H.nm_df, H.nm_df, H.nm_df]
    all_goals repeat' first | exact hb _ _ | apply Bd.smul | apply Bd.add | apply Bd.mul
  rw [e2] at key
  have cs : ∀ a b c d : ℤ × ℤ, mean (df W a b * df W c d) ≤ len W (a - b) * len W (c - d) := by
    intro a b c d
    rw [← H.nm_df, ← H.nm_df]
    exact mean_mul_le (hb _ _) (hb _ _)
  have c1 := cs X V X m
  have c2 := cs X V V m'
  have c3 := cs X V X k
  have c4 := cs X V V k'
  have c5 := cs Y U Y m
  have c6 := cs Y U U m'
  have c7 := cs Y U U k
  have c8 := cs Y U Y k'
  rw [one_div, inv_mul_eq_div] at key
  linarith

end Lip

end Cat
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Prices are nonpositively curved": means

The subsection "Means". For n = 1, 2, … a function W n is a price on two sheets of ℤ² (the type Bool × ℤ × ℤ) with
W n (P, P+g) ≤ Λ|g| on each sheet. The mean E is Cat.mean, the limit along a fixed free ultrafilter of the means over the
windows; it is linear, positive and invariant under translations (Nc/Cat/Mean.lean).
-/

namespace Paper

open Finset Filter Topology Nc.Price

variable {K : Type} [Field K]

/-- The paper's ν(g) = (E W(P,P+g)²)^(1/2). -/
noncomputable def meanLength (W : ℕ → (Bool × ℤ × ℤ) → (Bool × ℤ × ℤ) → ℝ) (g : ℤ × ℤ) : ℝ :=
  Cat.len (fun n b P P' => W n (b, P) (b, P')) g

/-- ν(g) is the square root of the limit along a fixed ultrafilter of the means of W(P, P+g)² over both sheets of the
n-th window. -/
theorem meanLength_eq (W : ℕ → (Bool × ℤ × ℤ) → (Bool × ℤ × ℤ) → ℝ) (g : ℤ × ℤ) :
    meanLength W g = √(limUnder (hyperfilter ℕ : Filter ℕ) fun n => (∑ b : Bool, ∑ i ∈ range (n ^ 2),
      ∑ j ∈ range n, W n (b, ((i : ℤ), (j : ℤ))) (b, ((i : ℤ), (j : ℤ)) + g) ^ 2) / (2 * n ^ 3)) := by
  simp only [meanLength, Cat.len, Cat.nm, Cat.mean, Cat.avg, Cat.df, Pi.mul_apply, add_zero, pow_two]

/-- The paper's N(g) = inf ν(Sg)/S over integers S ≥ 1. -/
noncomputable def meanNorm (W : ℕ → (Bool × ℤ × ℤ) → (Bool × ℤ × ℤ) → ℝ) (g : ℤ × ℤ) : ℝ :=
  sInf {r : ℝ | ∃ S : ℕ, 0 < S ∧ r = meanLength W (S • g) / S}

section Norm

variable (W : ℕ → (Bool × ℤ × ℤ) → (Bool × ℤ × ℤ) → ℝ) (g : ℤ × ℤ)

theorem meanLength_nonneg : 0 ≤ meanLength W g := Cat.nm_nonneg _

theorem meanNorm_isGLB : IsGLB {r : ℝ | ∃ S : ℕ, 0 < S ∧ r = meanLength W (S • g) / S} (meanNorm W g) :=
  isGLB_csInf ⟨_, 1, one_pos, rfl⟩
    ⟨0, by rintro _ ⟨S, -, rfl⟩; exact div_nonneg (meanLength_nonneg _ _) (Nat.cast_nonneg _)⟩

/-- "For upper bounds [on N it is enough to prove them] for one S." -/
theorem meanNorm_le {S : ℕ} (hS : 0 < S) : meanNorm W g ≤ meanLength W (S • g) / S :=
  (meanNorm_isGLB W g).1 ⟨S, hS, rfl⟩

theorem meanNorm_le_meanLength : meanNorm W g ≤ meanLength W g := by
  simpa using meanNorm_le W g one_pos

/-- "For lower bounds [on N] it is enough to prove them for ν(Sg)/S for every S." -/
theorem le_meanNorm {c : ℝ} (h : ∀ S : ℕ, 0 < S → c * S ≤ meanLength W (S • g)) : c ≤ meanNorm W g := by
  refine (meanNorm_isGLB W g).2 ?_
  rintro _ ⟨S, hS, rfl⟩
  rw [le_div_iff₀ (by exact_mod_cast hS)]
  exact h S hS

theorem meanNorm_nonneg : 0 ≤ meanNorm W g :=
  le_meanNorm W g fun S _ => by rw [zero_mul]; exact meanLength_nonneg _ _

end Norm

variable {W : ℕ → (Bool × ℤ × ℤ) → (Bool × ℤ × ℤ) → ℝ} {Λ : ℝ}

/-- What is used of the prices W n: they are pseudometrics, Lipschitz on each sheet, and satisfy (Q), which is Proposition
prop:crossing. -/
theorem lem_means_lip (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) :
    Cat.Lip (fun n b P P' => W n (b, P) (b, P')) Λ where
  nonneg n _ _ _ := (hW n).nonneg _ _
  self n _ _ := (hW n).self _
  symm n _ _ _ := (hW n).symm _ _
  tri n _ _ _ _ := (hW n).triangle _ _ _
  lip := hΛ
  q n b x v y u o o' w w' _ _ τ hp hq hτ :=
    eq_Q (hW n) (b, x) (b, v) (b, y) (b, u) (b, o) (b, o') (b, w) (b, w') hp hq τ hτ

/-- The text before Lemma lem:means: "By translation invariance and Minkowski's inequality ν is even …" -/
theorem lem_means_even (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) (g : ℤ × ℤ) :
    meanLength W (-g) = meanLength W g :=
  (lem_means_lip hW hΛ).len_neg g

/-- The text before Lemma lem:means: "… and subadditive". -/
theorem lem_means_subadditive (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) (g h : ℤ × ℤ) :
    meanLength W (g + h) ≤ meanLength W g + meanLength W h :=
  (lem_means_lip hW hΛ).len_add g h

/-- The first step of the proof of Lemma lem:means: "By the Cauchy–Schwarz inequality ν satisfies (Q) with the norms of
differences for the distances, p and q the norms of x − v and y − u." -/
theorem lem_means_Q (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|))
    (x v y u o o' w w' : ℤ × ℤ) {τ : ℝ} (hτ : 0 < τ) :
    2 * (meanLength W (x - v) ^ 2 + meanLength W (y - u) ^ 2) ≤
      meanLength W (x - v) *
        (meanLength W (x - o) + meanLength W (v - o') + meanLength W (x - w) + meanLength W (v - w'))
      + meanLength W (y - u) *
        (meanLength W (y - o) + meanLength W (u - o') + meanLength W (u - w) + meanLength W (y - w'))
      + τ * (meanLength W (x - v) ^ 2 + meanLength W (y - u) ^ 2)
      + (meanLength W (o - o') ^ 2 + meanLength W (w - w') ^ 2) / (2 * τ) :=
  (lem_means_lip hW hΛ).len_q x v y u o o' w w' τ hτ

/-- ν is an even subadditive function with (Q). -/
theorem meanLength_len (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) :
    Cat.Len (meanLength W) where
  nonneg := meanLength_nonneg W
  zero := (lem_means_lip hW hΛ).len_zero
  neg := lem_means_even hW hΛ
  add := lem_means_subadditive hW hΛ
  q x v y u o o' w w' _ hτ := lem_means_Q hW hΛ x v y u o o' w w' hτ

/-- N is an even subadditive function with (Q), and homogeneous. -/
theorem meanNorm_len (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) :
    Cat.Len (meanNorm W) ∧ Cat.Homog (meanNorm W) := by
  obtain ⟨N, hN, hom, hle, hgl⟩ := (meanLength_len hW hΛ).exists_homog
  have e : N = meanNorm W := by
    funext g
    refine le_antisymm (le_meanNorm W g fun S _ => ?_) (hgl g _ fun S hS => ?_)
    · rw [mul_comm, ← hom S g]
      exact hle _
    · have := meanNorm_le W g hS
      rwa [le_div_iff₀ (by exact_mod_cast hS)] at this
  exact e ▸ ⟨hN, hom⟩

/-- The definition of N: "N(g) = lim ν(Sg)/S = inf ν(Sg)/S." The limit exists and is the infimum, as ν is subadditive. -/
theorem lem_means_limit (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) (g : ℤ × ℤ) :
    Tendsto (fun S : ℕ => meanLength W (S • g) / S) atTop (𝓝 (meanNorm W g)) := by
  have hν := meanLength_len hW hΛ
  have hb : BddBelow (Set.range fun S : ℕ => meanLength W (S • g) / S) :=
    ⟨0, by rintro _ ⟨S, rfl⟩; exact div_nonneg (hν.nonneg _) (Nat.cast_nonneg _)⟩
  have ht := (hν.subadditive g).tendsto_lim hb
  have e : (hν.subadditive g).lim = meanNorm W g := by
    refine le_antisymm (le_meanNorm W g fun S hS => ?_) ?_
    · have := (hν.subadditive g).lim_le_div hb (n := S) hS.ne'
      rwa [le_div_iff₀ (by exact_mod_cast hS)] at this
    · exact ge_of_tendsto ht (eventually_atTop.2 ⟨1, fun S hS => meanNorm_le W g hS⟩)
  rwa [e] at ht

/-- The text before Lemma lem:means: "so N is also homogeneous". -/
theorem lem_means_homogeneous (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) (S : ℕ) (g : ℤ × ℤ) :
    meanNorm W (S • g) = S * meanNorm W g :=
  (meanNorm_len hW hΛ).2 S g

/-- The text before Lemma lem:means: N is even and subadditive, as ν is. With lem_means_homogeneous and meanNorm_nonneg this
makes N a seminorm on ℤ². -/
theorem lem_means_seminorm (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) :
    (∀ g, meanNorm W (-g) = meanNorm W g) ∧ ∀ g h, meanNorm W (g + h) ≤ meanNorm W g + meanNorm W h :=
  ⟨(meanNorm_len hW hΛ).1.neg, (meanNorm_len hW hΛ).1.add⟩

/-- The second step of the proof of Lemma lem:means: "Apply this to eight vectors multiplied by S, divide by S² and let
S → ∞: so does N, with the same τ." -/
theorem lem_means_Q_norm (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|))
    (x v y u o o' w w' : ℤ × ℤ) {τ : ℝ} (hτ : 0 < τ) :
    2 * (meanNorm W (x - v) ^ 2 + meanNorm W (y - u) ^ 2) ≤
      meanNorm W (x - v) * (meanNorm W (x - o) + meanNorm W (v - o') + meanNorm W (x - w) + meanNorm W (v - w'))
      + meanNorm W (y - u) * (meanNorm W (y - o) + meanNorm W (u - o') + meanNorm W (u - w) + meanNorm W (y - w'))
      + τ * (meanNorm W (x - v) ^ 2 + meanNorm W (y - u) ^ 2)
      + (meanNorm W (o - o') ^ 2 + meanNorm W (w - w') ^ 2) / (2 * τ) :=
  (meanNorm_len hW hΛ).1.q x v y u o o' w w' τ hτ

/-! ### The proof of Lemma lem:means

The steps after "so does N" use of N only that it is even, subadditive and homogeneous and satisfies (Q). This is
Cat.Len N and Cat.Homog N, and it holds for N = meanNorm W by lem_means_seminorm, lem_means_homogeneous and
lem_means_Q_norm. As in the paper c = a + b, e = a − b, f = N(c), f′ = N(e). -/

section Parallelogram

/-- "∂p = 2N(p) − N(p−a) − N(p−b)". The paper's ∂′q = 2N(q) − N(q−a) − N(q+b) is the same with −b for b. -/
def meansDiff (N : ℤ × ℤ → ℝ) (a b p : ℤ × ℤ) : ℝ := 2 * N p - N (p - a) - N (p - b)

/-- "A_i = Mc + ie". With −b for b this is Me + ic. -/
def meansPt (a b : ℤ × ℤ) (M i : ℕ) : ℤ × ℤ := M • (a + b) + i • (a - b)

/-- "δ_i = N(A_i − a) − N(A_i − 2a)". -/
def meansDelta (N : ℤ × ℤ → ℝ) (a b : ℤ × ℤ) (M i : ℕ) : ℝ :=
  N (meansPt a b M i - a) - N (meansPt a b M i - a - a)

variable {N : ℤ × ℤ → ℝ}

/-- "Take (x,v,y,u) = (p,−p,q,−q) and (o,o′,w,w′) = (a,−a,b,−b) and divide by 4:
N(p)∂p + N(q)∂′q ≤ τ(N(p)² + N(q)²) + (N(a)² + N(b)²)/(2τ)." -/
theorem lem_means_display (hN : Cat.Len N) (hh : Cat.Homog N) (a b p q : ℤ × ℤ) {τ : ℝ} (hτ : 0 < τ) :
    N p * meansDiff N a b p + N q * meansDiff N a (-b) q ≤
      τ * (N p ^ 2 + N q ^ 2) + (N a ^ 2 + N b ^ 2) / (2 * τ) := by
  unfold meansDiff
  have h := hN.q p (-p) q (-q) a (-a) b (-b) τ hτ
  have e1 : ∀ Z : ℤ × ℤ, N (Z - -Z) = 2 * N Z := by
    intro Z
    rw [show Z - -Z = 2 • Z by module, hh]
    norm_num
  have e2 : N (-p - -a) = N (p - a) := by rw [← hN.neg]; congr 1; module
  have e3 : N (-p - -b) = N (p - b) := by rw [← hN.neg]; congr 1; module
  have e4 : N (-q - -a) = N (q - a) := by rw [← hN.neg]; congr 1; module
  have e5 : N (-q - b) = N (q - -b) := by rw [← hN.neg]; congr 1; module
  rw [e1 p, e1 q, e1 a, e1 b, e2, e3, e4, e5] at h
  have e6 : ((2 * N a) ^ 2 + (2 * N b) ^ 2) / (2 * τ) = 4 * ((N a ^ 2 + N b ^ 2) / (2 * τ)) := by
    ring
  rw [e6] at h
  linarith

/-- "∂A_i + ∂(A_i − a) = 2(N(A_i) − N(A_i − c)) + δ_i − δ_{i+1}." This holds for every function N. -/
theorem lem_means_identity (a b : ℤ × ℤ) (M i : ℕ) :
    meansDiff N a b (meansPt a b M i) + meansDiff N a b (meansPt a b M i - a) =
      2 * (N (meansPt a b M i) - N (meansPt a b M i - (a + b)))
        + (meansDelta N a b M i - meansDelta N a b M (i + 1)) := by
  simp only [meansDiff, meansDelta, meansPt]
  have e1 : M • (a + b) + (i + 1) • (a - b) - a = M • (a + b) + i • (a - b) - b := by module
  have e2 : M • (a + b) + i • (a - b) - b - a = M • (a + b) + i • (a - b) - (a + b) := by module
  have e3 : M • (a + b) + i • (a - b) - a - b = M • (a + b) + i • (a - b) - (a + b) := by module
  rw [e1, e2, e3]
  ring

/-- "As t ↦ N(tc + ie) is convex, the first difference on the right is at least f − 2N(ie)/M." Here s stands for ie, and
convexity is used at the integers t ≥ 0: the differences N((t+1)c + s) − N(tc + s) do not decrease. -/
theorem lem_means_convex (hN : Cat.Len N) (hh : Cat.Homog N) (s c : ℤ × ℤ) (M : ℕ) (hM : 0 < M) :
    N c - 2 * N s / M ≤ N (M • c + s) - N (M • c + s - c) := by
  have hmono : Monotone fun t : ℕ => N ((t + 1) • c + s) - N (t • c + s) := by
    refine monotone_nat_of_le_succ fun t => ?_
    have h1 := hN.add ((t + 1 + 1) • c + s) (t • c + s)
    have h2 : (t + 1 + 1) • c + s + (t • c + s) = 2 • ((t + 1) • c + s) := by module
    rw [h2, hh] at h1
    push_cast at h1
    linarith
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have h1 := Finset.sum_range_sub (fun t : ℕ => N (t • c + s)) (M + 1)
  have h2 : ∑ t ∈ range (M + 1), (N ((t + 1) • c + s) - N (t • c + s)) ≤
      ∑ t ∈ range (M + 1), (N ((M + 1) • c + s) - N (M • c + s)) :=
    Finset.sum_le_sum fun t ht => hmono (by simpa [Nat.lt_succ_iff] using ht)
  rw [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul (α := ℝ), zero_smul, zero_add] at h2
  have h3 := hN.sub_le ((M + 1) • c + s) s
  rw [add_sub_cancel_right, hh] at h3
  have h4 : (M + 1) • c + s - c = M • c + s := by module
  rw [h4]
  have hM' : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have h5 : N c - 2 * N s / ((M + 1 : ℕ) : ℝ) =
      (((M + 1 : ℕ) : ℝ) * N c - 2 * N s) / ((M + 1 : ℕ) : ℝ) := by field_simp
  rw [h5, div_le_iff₀ hM']
  linarith

/-- "The δ_i are bounded and telescope": the sum of ∂A_i + ∂(A_i − a) over 0 ≤ i < R is at least
2R(f − 2R·f′/M) − 2N(a). -/
theorem lem_means_telescope (hN : Cat.Len N) (hh : Cat.Homog N) (a b : ℤ × ℤ) {M : ℕ} (hM : 0 < M) (R : ℕ) :
    2 * R * (N (a + b) - 2 * R * N (a - b) / M) - 2 * N a ≤
      ∑ i ∈ range R, (meansDiff N a b (meansPt a b M i) + meansDiff N a b (meansPt a b M i - a)) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have h2 : ∀ i ∈ range R, 2 * (N (a + b) - 2 * R * N (a - b) / M)
      + (meansDelta N a b M i - meansDelta N a b M (i + 1)) ≤
        meansDiff N a b (meansPt a b M i) + meansDiff N a b (meansPt a b M i - a) := by
    intro i hi
    rw [lem_means_identity]
    have h3 := lem_means_convex hN hh (i • (a - b)) (a + b) M hM
    rw [hh] at h3
    have h4 : 2 * ((i : ℝ) * N (a - b)) / M ≤ 2 * R * N (a - b) / M := by
      apply div_le_div_of_nonneg_right _ hM'.le
      have : (i : ℝ) ≤ R := by exact_mod_cast (Finset.mem_range.1 hi).le
      nlinarith [hN.nonneg (a - b)]
    simp only [meansPt]
    linarith
  have h5 := Finset.sum_le_sum h2
  rw [Finset.sum_add_distrib, Finset.sum_range_sub', Finset.sum_const, Finset.card_range,
    nsmul_eq_mul (α := ℝ)] at h5
  have h6 : meansDelta N a b M R ≤ N a := by
    unfold meansDelta
    linarith [hN.le_add_sub (meansPt a b M R - a) a]
  have h7 : -N a ≤ meansDelta N a b M 0 := by
    unfold meansDelta
    linarith [hN.sub_le (meansPt a b M 0 - a) a]
  linarith

/-- N(p) = Mf + O(R) at the points p = Mc + ie and p = Mc + ie − a with i < R: the error is at most 2Rκ if N(a), N(e) ≤ κ. -/
theorem lem_means_near (hN : Cat.Len N) (hh : Cat.Homog N) {a c e : ℤ × ℤ} {κ : ℝ} (ha : N a ≤ κ) (he : N e ≤ κ)
    (M : ℕ) {R i : ℕ} (hi : i < R) :
    |N (M • c + i • e) - M * N c| ≤ 2 * R * κ ∧ |N (M • c + i • e - a) - M * N c| ≤ 2 * R * κ := by
  have hi' : (i : ℝ) + 1 ≤ R := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  rw [← hh]
  constructor
  · have h1 := hN.abs_sub_le (M • c + i • e) (M • c)
    rw [add_sub_cancel_left, hh i e] at h1
    nlinarith [hN.nonneg e]
  · have h1 := hN.abs_sub_le (M • c + i • e - a) (M • c)
    have h2 : M • c + i • e - a - M • c = i • e - a := by module
    rw [h2] at h1
    have h3 := hN.sub_le (i • e) a
    rw [hh i e] at h3
    nlinarith [hN.nonneg e]

/-- "∂ is bounded by N(a) + N(b), so N(p)∂p = Mf∂p + O(R)", and the same for ∂′ at q, with f′. "With τ = 1/(2M)" the
display becomes Mf∂p + Mf′∂′q ≤ M(½(f² + f′²) + N(a)² + N(b)²) + O(R). Here f = N(c), f′ = N(e), the points p, q have
N(p) = Mf + O(R), N(q) = Mf′ + O(R) with errors at most 2Rκ, and the last O(R) is 12Rκ². -/
theorem lem_means_estimate (hN : Cat.Len N) (hh : Cat.Homog N) (a b p q c e : ℤ × ℤ) {M R : ℕ} {κ : ℝ} (hM : 0 < M)
    (hR : R ≤ M) (hκ : N a + N b ≤ κ) (hc : N c ≤ κ) (he : N e ≤ κ)
    (hp : |N p - M * N c| ≤ 2 * R * κ) (hq : |N q - M * N e| ≤ 2 * R * κ) :
    M * N c * meansDiff N a b p + M * N e * meansDiff N a (-b) q ≤
      M * ((N c ^ 2 + N e ^ 2) / 2 + (N a ^ 2 + N b ^ 2)) + 12 * R * κ ^ 2 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hR' : (R : ℝ) ≤ M := by exact_mod_cast hR
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hκ0 : 0 ≤ κ := (hN.nonneg c).trans hc
  have h1 := lem_means_display hN hh a b p q (τ := 1 / (2 * M)) (by positivity)
  have e1 : (N a ^ 2 + N b ^ 2) / (2 * (1 / (2 * (M : ℝ)))) = M * (N a ^ 2 + N b ^ 2) := by
    field_simp
  rw [e1] at h1
  have hxp : |meansDiff N a b p| ≤ κ := by
    unfold meansDiff
    have h2 := hN.abs_sub_le p (p - a)
    have h3 := hN.abs_sub_le p (p - b)
    rw [sub_sub_cancel] at h2 h3
    rw [abs_le] at h2 h3 ⊢
    constructor <;> linarith
  have hxq : |meansDiff N a (-b) q| ≤ κ := by
    unfold meansDiff
    have h2 := hN.abs_sub_le q (q - a)
    have h3 := hN.abs_sub_le q (q - -b)
    rw [sub_sub_cancel] at h2 h3
    rw [hN.neg] at h3
    rw [abs_le] at h2 h3 ⊢
    constructor <;> linarith
  have low : ∀ (A B x : ℝ), |A - B| ≤ 2 * R * κ → |x| ≤ κ → B * x - 2 * R * κ ^ 2 ≤ A * x := by
    intro A B x hA hx
    have h2 : |(A - B) * x| ≤ 2 * R * κ * κ := by
      rw [abs_mul]
      exact mul_le_mul hA hx (abs_nonneg _) (by positivity)
    have h3 := (abs_le.1 h2).1
    nlinarith
  have sq : ∀ (Z c : ℤ × ℤ), N c ≤ κ → |N Z - M * N c| ≤ 2 * R * κ →
      1 / (2 * M) * N Z ^ 2 ≤ M * N c ^ 2 / 2 + 4 * R * κ ^ 2 := by
    intro Z c hc hZ
    have h2 : N Z ≤ M * N c + 2 * R * κ := by linarith [(abs_le.1 hZ).2]
    have h3 : N Z ^ 2 ≤ (M * N c + 2 * R * κ) ^ 2 := pow_le_pow_left₀ (hN.nonneg Z) h2 2
    have h4 : (M * N c + 2 * R * κ) ^ 2 ≤ M ^ 2 * N c ^ 2 + 8 * M * R * κ ^ 2 := by
      have h5 : (M : ℝ) * R * (N c * κ) ≤ M * R * κ ^ 2 := by
        rw [sq κ]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hκ0) (by positivity)
      have h6 : (R : ℝ) * R * κ ^ 2 ≤ M * R * κ ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hR' hR0) (sq_nonneg _)
      nlinarith
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  have l1 := low _ _ _ hp hxp
  have l2 := low _ _ _ hq hxq
  have s1 := sq _ _ hc hp
  have s2 := sq _ _ he hq
  linarith

/-- The arithmetic of "averaging over i and dividing by 2M", with M = m², f, f′, n = N(a) at most κ, Q = N(a)² + N(b)². -/
private theorem means_arith {m f f' n Q κ : ℝ} (hm : 0 < m) (hf0 : 0 ≤ f) (hf : f ≤ κ) (hf0' : 0 ≤ f') (hf' : f' ≤ κ)
    (hn0 : 0 ≤ n) (hn : n ≤ κ)
    (h : m ^ 2 * f * (2 * m * (f - 2 * m * f' / m ^ 2) - 2 * n)
        + m ^ 2 * f' * (2 * m * (f' - 2 * m * f / m ^ 2) - 2 * n) ≤
      m * (m ^ 2 * ((f ^ 2 + f' ^ 2) / 2 + Q) + 12 * m * κ ^ 2
        + (m ^ 2 * ((f ^ 2 + f' ^ 2) / 2 + Q) + 12 * m * κ ^ 2))) :
    f ^ 2 + f' ^ 2 ≤ 2 * Q + 36 * κ ^ 2 * (1 / m) := by
  have hκ0 : 0 ≤ κ := hf0.trans hf
  have q1 : f * f' ≤ κ ^ 2 := by rw [sq]; exact mul_le_mul hf hf' hf0' hκ0
  have q2 : f * n ≤ κ ^ 2 := by rw [sq]; exact mul_le_mul hf hn hn0 hκ0
  have q3 : f' * n ≤ κ ^ 2 := by rw [sq]; exact mul_le_mul hf' hn hn0 hκ0
  have e3 : m ^ 2 * f * (2 * m * (f - 2 * m * f' / m ^ 2) - 2 * n) =
      2 * m ^ 3 * f ^ 2 - 4 * (f * f') * m ^ 2 - 2 * (f * n) * m ^ 2 := by
    field_simp
    ring
  have e4 : m ^ 2 * f' * (2 * m * (f' - 2 * m * f / m ^ 2) - 2 * n) =
      2 * m ^ 3 * f' ^ 2 - 4 * (f * f') * m ^ 2 - 2 * (f' * n) * m ^ 2 := by
    field_simp
    ring
  rw [e3, e4] at h
  have h5 : m ^ 3 * (f ^ 2 + f' ^ 2) ≤ m ^ 3 * (2 * Q + 36 * κ ^ 2 * (1 / m)) := by
    have e5 : m ^ 3 * (2 * Q + 36 * κ ^ 2 * (1 / m)) = 2 * m ^ 3 * Q + 36 * κ ^ 2 * m ^ 2 := by
      field_simp
    rw [e5]
    have w1 := mul_le_mul_of_nonneg_right q1 (sq_nonneg m)
    have w2 := mul_le_mul_of_nonneg_right q2 (sq_nonneg m)
    have w3 := mul_le_mul_of_nonneg_right q3 (sq_nonneg m)
    linarith
  exact le_of_mul_le_mul_left h5 (by positivity)

/-- "With τ = 1/(2M), adding the two inequalities, averaging over i and dividing by 2M gives
f² + f′² ≤ ½(f² + f′²) + N(a)² + N(b)² + O(1/R)", where M = R². Here the inequality is doubled and ½(f² + f′²) is
subtracted, and the O(1/R) becomes 36(N(a) + N(b))²/R. -/
theorem lem_means_average (hN : Cat.Len N) (hh : Cat.Homog N) (a b : ℤ × ℤ) {R : ℕ} (hR : 0 < R) :
    N (a + b) ^ 2 + N (a - b) ^ 2 ≤ 2 * (N a ^ 2 + N b ^ 2) + 36 * (N a + N b) ^ 2 * (1 / (R : ℝ)) := by
  set κ := N a + N b with hκ
  have hc : N (a + b) ≤ κ := hN.add a b
  have he : N (a - b) ≤ κ := hN.sub_le a b
  have ha : N a ≤ κ := by linarith [hN.nonneg b]
  have hM : 0 < R ^ 2 := by positivity
  have hRM : R ≤ R ^ 2 := by nlinarith
  have s1 := lem_means_telescope hN hh a b hM R
  have s2 := lem_means_telescope hN hh a (-b) hM R
  simp only [meansPt] at s1 s2
  rw [sub_neg_eq_add, ← sub_eq_add_neg] at s2
  have p : ∀ i ∈ range R, _ := fun i hi => add_le_add
    (lem_means_estimate hN hh a b _ _ (a + b) (a - b) hM hRM le_rfl hc he
      (lem_means_near hN hh ha he _ (Finset.mem_range.1 hi)).1 (lem_means_near hN hh ha hc _ (Finset.mem_range.1 hi)).1)
    (lem_means_estimate hN hh a b _ _ (a + b) (a - b) hM hRM le_rfl hc he
      (lem_means_near hN hh ha he _ (Finset.mem_range.1 hi)).2 (lem_means_near hN hh ha hc _ (Finset.mem_range.1 hi)).2)
  have hp := Finset.sum_le_sum p
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul (α := ℝ)] at hp
  have hp2 : ((R ^ 2 : ℕ) : ℝ) * N (a + b) *
        (2 * R * (N (a + b) - 2 * R * N (a - b) / (R ^ 2 : ℕ)) - 2 * N a)
      + ((R ^ 2 : ℕ) : ℝ) * N (a - b) *
        (2 * R * (N (a - b) - 2 * R * N (a + b) / (R ^ 2 : ℕ)) - 2 * N a) ≤
      R * (((R ^ 2 : ℕ) : ℝ) * ((N (a + b) ^ 2 + N (a - b) ^ 2) / 2 + (N a ^ 2 + N b ^ 2))
        + 12 * R * κ ^ 2 + (((R ^ 2 : ℕ) : ℝ) * ((N (a + b) ^ 2 + N (a - b) ^ 2) / 2
        + (N a ^ 2 + N b ^ 2)) + 12 * R * κ ^ 2)) := by
    refine le_trans ?_ hp
    refine le_trans (add_le_add
      (mul_le_mul_of_nonneg_left s1 (mul_nonneg (Nat.cast_nonneg _) (hN.nonneg _)))
      (mul_le_mul_of_nonneg_left s2 (mul_nonneg (Nat.cast_nonneg _) (hN.nonneg _)))) ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => le_of_eq (by ring)
  push_cast at hp2
  exact means_arith (by exact_mod_cast hR) (hN.nonneg _) hc (hN.nonneg _) he (hN.nonneg _) ha hp2

/-- "Thus N(a+b)² + N(a−b)² ≤ 2N(a)² + 2N(b)²." -/
theorem lem_means_parallelogram_le (hN : Cat.Len N) (hh : Cat.Homog N) (a b : ℤ × ℤ) :
    N (a + b) ^ 2 + N (a - b) ^ 2 ≤ 2 * (N a ^ 2 + N b ^ 2) := by
  have h1 : Tendsto (fun R : ℕ => 2 * (N a ^ 2 + N b ^ 2) + 36 * (N a + N b) ^ 2 * (1 / (R : ℝ))) atTop
      (𝓝 (2 * (N a ^ 2 + N b ^ 2) + 36 * (N a + N b) ^ 2 * 0)) :=
    (tendsto_one_div_atTop_nhds_zero_nat.const_mul _).const_add _
  rw [mul_zero, add_zero] at h1
  refine ge_of_tendsto h1 ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact lem_means_average hN hh a b hR

end Parallelogram

/-- **Paper: Lemma lem:means.** For prices W_n on two sheets of ℤ² with W_n(P,P+g) ≤ Λ|g| for points of one sheet, and
N(g) = lim ν(Sg)/S = inf ν(Sg)/S: "N(a+b)² + N(a−b)² = 2N(a)² + 2N(b)² for all a, b ∈ ℤ²." -/
theorem lem_means (W : ℕ → (Bool × ℤ × ℤ) → (Bool × ℤ × ℤ) → ℝ) (hW : ∀ n, IsPrice K (W n)) (Λ : ℝ)
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) :
    ∃ N : ℤ × ℤ → ℝ,
      (∀ g, Tendsto (fun S : ℕ => meanLength W (S • g) / S) atTop (𝓝 (N g)) ∧
        IsGLB {r : ℝ | ∃ S : ℕ, 0 < S ∧ r = meanLength W (S • g) / S} (N g)) ∧
      ∀ a b, N (a + b) ^ 2 + N (a - b) ^ 2 = 2 * N a ^ 2 + 2 * N b ^ 2 := by
  refine ⟨meanNorm W, fun g => ⟨lem_means_limit hW hΛ g, meanNorm_isGLB W g⟩, fun a b => ?_⟩
  have hom : Cat.Homog (meanNorm W) := lem_means_homogeneous hW hΛ
  have hN : Cat.Len (meanNorm W) :=
    { nonneg := meanNorm_nonneg W
      zero := by simpa using hom 0 0
      neg := (lem_means_seminorm hW hΛ).1
      add := (lem_means_seminorm hW hΛ).2
      q := fun x v y u o o' w w' _ hτ => lem_means_Q_norm hW hΛ x v y u o o' w w' hτ }
  refine le_antisymm (by linarith [lem_means_parallelogram_le hN hom a b]) ?_
  -- "applied to a+b, a−b it gives equality"
  have h := lem_means_parallelogram_le hN hom (a + b) (a - b)
  rw [show a + b + (a - b) = (2 : ℕ) • a by rw [two_nsmul]; abel,
    show a + b - (a - b) = (2 : ℕ) • b by rw [two_nsmul]; abel, hom, hom] at h
  push_cast at h
  linarith

/-- Lemma lem:means for the function N = meanNorm W. -/
theorem lem_means_norm (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) (a b : ℤ × ℤ) :
    meanNorm W (a + b) ^ 2 + meanNorm W (a - b) ^ 2 = 2 * meanNorm W a ^ 2 + 2 * meanNorm W b ^ 2 := by
  obtain ⟨N, hN, h⟩ := lem_means W hW Λ hΛ
  have e : N = meanNorm W := funext fun g => (hN g).2.unique (meanNorm_isGLB W g)
  rw [← e]
  exact h a b

end Paper
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Windows: clamping, the relative place in a window, and two elementary inequalities

Helpers for the proof of Theorem thm:cn (Paper/Fan.lean); nothing here is about prices.
-/

open Filter Topology Finset

namespace Cat

theorem sum_lt {M j : ℕ} (hj : j ≤ M) (x y : ℝ) :
    ∑ l : Fin M, (if (l : ℕ) < j then x else y) = j * x + ((M : ℝ) - j) * y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Fin.sum_univ_eq_sum_range (fun l => if l < j then x else y), Finset.sum_range_add]
  have h1 : ∑ l ∈ range j, (if l < j then x else y) = ∑ l ∈ range j, x :=
    Finset.sum_congr rfl fun l hl => if_pos (Finset.mem_range.1 hl)
  have h2 : ∑ l ∈ range d, (if j + l < j then x else y) = ∑ l ∈ range d, y :=
    Finset.sum_congr rfl fun l _ => if_neg (by omega)
  rw [h1, h2]
  simp

/-- Clamping an integer to `0, …, N`. -/
def cl (N : ℕ) (i : ℤ) : ℕ := min i.toNat N

theorem cl_le (N : ℕ) (i : ℤ) : cl N i ≤ N := min_le_right _ _

theorem cl_sub (N : ℕ) (i i' : ℤ) : |((cl N i : ℕ) : ℝ) - (cl N i' : ℕ)| ≤ |(i : ℝ) - i'| := by
  have h : |((cl N i : ℕ) : ℤ) - (cl N i' : ℕ)| ≤ |i - i'| := by
    unfold cl
    rcases le_total i i' with h | h
    · rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]
      omega
    · rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
      omega
  exact_mod_cast h

theorem cl_cast {N : ℕ} {i : ℤ} (h0 : 0 ≤ i) (h1 : i ≤ N) : ((cl N i : ℕ) : ℝ) = i := by
  have : ((cl N i : ℕ) : ℤ) = i := by
    unfold cl
    omega
  exact_mod_cast this

theorem cl_window {n T : ℕ} {i k : ℤ} (h0 : 0 ≤ i + k + n) (h1 : i + k + n ≤ n ^ 2 * T) :
    ((cl (n ^ 2 * T) (i + k + n) : ℕ) : ℝ) = i + k + n := by
  rw [cl_cast h0 (by exact_mod_cast h1)]
  push_cast
  ring

theorem cl_succ (N : ℕ) (i : ℤ) : |((cl N i : ℕ) : ℝ) - (cl N (i + 1) : ℕ)| ≤ 1 := by
  refine (cl_sub _ _ _).trans ?_
  push_cast
  rw [sub_add_cancel_left, abs_neg, abs_one]

theorem cl_sq (n : ℕ) : cl (n ^ 2) ((n : ℤ) ^ 2) = n ^ 2 := by
  have : ((n : ℤ) ^ 2) = ((n ^ 2 : ℕ) : ℤ) := by push_cast; rfl
  rw [this, cl, Int.toNat_natCast, min_self]

theorem cl_zero (N : ℕ) : cl N 0 = 0 := by simp [cl]

theorem max_one_pos (n : ℕ) : 0 < max n 1 := by simp

/-- What "n large" means below. -/
theorem eventually_large {T : ℕ} (hT : 2 ≤ T) (R : ℕ) : ∀ᶠ n : ℕ in atTop, max n 1 = n ∧ (1 : ℝ) ≤ n ∧ R ≤ n ∧
    n ^ 2 + 2 * n ≤ n ^ 2 * T ∧ n ^ 2 + 2 * n ≤ 2 * n ^ 2 := by
  filter_upwards [eventually_ge_atTop (max R 3)] with n hn
  have h3 : 3 ≤ n := (le_max_right _ _).trans hn
  have h4 : n ^ 2 + 2 * n ≤ 2 * n ^ 2 := by nlinarith
  refine ⟨by omega, by exact_mod_cast (by omega : 1 ≤ n), (le_max_left _ _).trans hn, ?_, h4⟩
  nlinarith

theorem prod_add_mk (i k : ℤ) (h : ℤ × ℤ) : ((i, k) : ℤ × ℤ) + h = (i + h.1, k + h.2) := rfl

/-- The relative place in the window. -/
noncomputable def place : Fn := fun n _ i _ => (cl (n ^ 2) i : ℕ) / (n : ℝ) ^ 2

theorem place_nonneg (n : ℕ) (b : Bool) (i k : ℤ) : 0 ≤ place n b i k := by
  unfold place
  positivity

theorem place_le_one (n : ℕ) (b : Bool) (i k : ℤ) : place n b i k ≤ 1 := by
  unfold place
  apply div_le_one_of_le₀ _ (by positivity)
  exact_mod_cast cl_le (n ^ 2) i

theorem bd_place : Bd place :=
  ⟨1, fun n b i k => by rw [abs_of_nonneg (place_nonneg _ _ _ _)]; exact place_le_one _ _ _ _⟩

theorem sum_id (N : ℕ) : ∑ i ∈ range N, (i : ℝ) = N * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem mean_place : mean place = 1 / 2 := by
  apply mean_eq bd_place
  have h1 : Tendsto (fun n : ℕ => 1 / 2 - 1 / 2 * (1 / (n : ℝ)) ^ 2) atTop
      (𝓝 (1 / 2 - 1 / 2 * 0 ^ 2)) :=
    ((tendsto_one_div_atTop_nhds_zero_nat.pow 2).const_mul _).const_sub _
  norm_num at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have h2 : ∀ b : Bool, ∑ i ∈ range (n ^ 2), ∑ k ∈ range n, place n b (i : ℕ) (k : ℕ) =
      n * (((n ^ 2 : ℕ) : ℝ) * ((n ^ 2 : ℕ) - 1) / 2 / n ^ 2) := by
    intro b
    rw [← sum_id, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hp : ∀ k ∈ range n, place n b (i : ℕ) (k : ℕ) = (i : ℝ) / n ^ 2 := by
      intro k _
      rw [place, cl_cast (Int.natCast_nonneg i) (by exact_mod_cast (Finset.mem_range.1 hi).le)]
      push_cast
      rfl
    rw [Finset.sum_congr rfl hp, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [avg, Finset.sum_congr rfl fun b _ => h2 b, Finset.sum_const, Finset.card_univ,
    Fintype.card_bool, nsmul_eq_mul]
  push_cast
  field_simp

/-- A sequence f with second differences at most `2ω`, where `φ` stands for the value f(−1): then
f(A) ≤ f(0) + A(f(0) − φ + ω) + A²ω. For ψ(l) = f(l) − l²ω this says ψ(A) ≤ ψ(0) + A(ψ(0) − ψ(−1)). -/
theorem conc {f : ℕ → ℝ} {φ ω : ℝ} (h0 : f 1 + φ ≤ 2 * f 0 + 2 * ω)
    (h : ∀ j, f (j + 2) + f j ≤ 2 * f (j + 1) + 2 * ω) (A : ℕ) :
    f A ≤ f 0 + A * (f 0 - φ + ω) + A ^ 2 * ω := by
  have key : ∀ j, f (j + 1) - f j ≤ (f 0 - φ + ω) + (2 * j + 1) * ω := by
    intro j
    induction j with
    | zero => norm_num; linarith
    | succ j ih => have := h j; push_cast; linarith
  induction A with
  | zero => simp
  | succ A ih => have := key A; push_cast; nlinarith

/-- Squaring |rn²(L′ − L) + aL′| ≤ W, with 2L′(L′ − L) ≥ L′² − L², 1 − r ≤ 2θ and n²(L′² − L²) ≤ K:
W² ≥ a²L′² + a·n²(L′² − L²) − 2aθK. -/
theorem sq_core {n L' L0 r a θ K W : ℝ} (hr0 : 0 ≤ r) (hr2 : 0 ≤ 1 - r) (hr1 : 1 - r ≤ 2 * θ)
    (ha : 0 ≤ a) (hK : 0 ≤ K) (hZ : n ^ 2 * (L' ^ 2 - L0 ^ 2) ≤ K)
    (h1 : r * (n ^ 2 * (L' - L0)) + a * L' ≤ W) (h2 : -(r * (n ^ 2 * (L' - L0)) + a * L') ≤ W) :
    a ^ 2 * (L' * L') + a * (n ^ 2 * (L' ^ 2 - L0 ^ 2)) - a * (2 * θ * K) ≤ W * W := by
  have E3 : (r * (n ^ 2 * (L' - L0)) + a * L') ^ 2 ≤ W ^ 2 := sq_le_sq' (by linarith) h1
  have Z2 : (1 - r) * (n ^ 2 * (L' ^ 2 - L0 ^ 2)) ≤ 2 * θ * K :=
    (mul_le_mul_of_nonneg_left hZ hr2).trans (mul_le_mul_of_nonneg_right hr1 hK)
  have Z4 : 0 ≤ a * r * (n ^ 2 * (L' - L0) ^ 2) := mul_nonneg (mul_nonneg ha hr0) (by positivity)
  have Z5 := mul_le_mul_of_nonneg_left Z2 ha
  have Z6 : 0 ≤ (r * (n ^ 2 * (L' - L0))) ^ 2 := sq_nonneg _
  nlinarith

end Cat
end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Prices are nonpositively curved": the proof of Theorem thm:cn

The fan, its four estimates, the claims (i) to (iv) on the seminorm N of the fan, and the end of the proof. The two sheets
are indexed by Bool; x true and x false are the paper's x and v, and θ = 1/T.
-/

namespace Paper

open Finset Filter Topology Nc.Price Cat

variable {K : Type} [Field K] {Y : Type} {w : Y → Y → ℝ}

/-- Points at distance 0 have the same distances from all points. -/
theorem dist_congr_of_zero (hw : IsPrice K w) {a b : Y} (h : w a b = 0) (c : Y) : w a c = w b c := by
  have h1 := hw.triangle a b c
  have h2 := hw.triangle b a c
  rw [hw.symm b a] at h2
  linarith

/-- Steps of length at most c add up. -/
theorem dist_chain_le (hw : IsPrice K w) (p : ℕ → Y) {c : ℝ} {M : ℕ} (h : ∀ i < M, w (p i) (p (i + 1)) ≤ c)
    (i i' : ℕ) (hi : i ≤ M) (hi' : i' ≤ M) : w (p i) (p i') ≤ |(i : ℝ) - i'| * c := by
  have key : ∀ i l, i + l ≤ M → w (p i) (p (i + l)) ≤ l * c := by
    intro i l
    induction l with
    | zero => intro _; simp [hw.self]
    | succ l ih =>
      intro hl
      have h1 := hw.triangle (p i) (p (i + l)) (p (i + l + 1))
      have h2 := h (i + l) (by omega)
      have h3 := ih (by omega)
      rw [← add_assoc]
      push_cast
      linarith
  rcases le_total i i' with hii | hii
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hii
    have : |(i : ℝ) - (i + l : ℕ)| = l := by
      push_cast
      rw [sub_add_cancel_left, abs_neg, abs_of_nonneg (Nat.cast_nonneg l)]
    rw [this]
    exact key i l hi'
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hii
    have : |((i' + l : ℕ) : ℝ) - i'| = l := by
      push_cast
      rw [add_sub_cancel_left, abs_of_nonneg (Nat.cast_nonneg l)]
    rw [this, hw.symm]
    exact key i' l hi

/-- New points on segments, by Proposition prop:random: for every q the point (q, j), 0 ≤ j ≤ M, is placed at b q with
probability j/M and otherwise at a q, "with one random number for all". -/
theorem thm_cn_segments (hw : IsPrice K w) {Q : Type} (a b : Q → Y) {M : ℕ} (hM : 0 < M) :
    ∃ w' : Y ⊕ (Q × ℕ) → Y ⊕ (Q × ℕ) → ℝ, IsPrice K w' ∧
      (∀ y y', w' (Sum.inl y) (Sum.inl y') = w y y') ∧
      (∀ q q' j, j ≤ M → w' (Sum.inr (q, j)) (Sum.inr (q', j)) ≤
        (1 - j / M) * w (a q) (a q') + j / M * w (b q) (b q')) ∧
      (∀ q j j', j ≤ j' → j' ≤ M → w' (Sum.inr (q, j)) (Sum.inr (q, j')) ≤
        ((j' : ℝ) - j) / M * w (a q) (b q)) ∧
      (∀ q j, j ≤ M → w' (Sum.inl (a q)) (Sum.inr (q, j)) ≤ j / M * w (a q) (b q)) ∧
      (∀ q j, j ≤ M → w' (Sum.inl (b q)) (Sum.inr (q, j)) ≤ (1 - j / M) * w (a q) (b q)) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨w', h1, h2, h3⟩ := prop_random_finite hw (Λ := Fin M) (fun _ => 1 / (M : ℝ)) (fun _ => by positivity)
    (by simp [hM'.ne']) (fun l (κ : Q × ℕ) => if (l : ℕ) < κ.2 then b κ.1 else a κ.1)
  refine ⟨w', h1, h2, ?_, ?_, ?_, ?_⟩
  · intro q q' j hj
    refine (h3 _ _).trans (le_of_eq ?_)
    simp only [Sum.elim_inr, ← Finset.mul_sum]
    have : ∀ l : Fin M, w (if (l : ℕ) < j then b q else a q) (if (l : ℕ) < j then b q' else a q') =
        if (l : ℕ) < j then w (b q) (b q') else w (a q) (a q') := by
      intro l
      split_ifs <;> rfl
    simp only [this, sum_lt hj]
    field_simp
    ring
  · intro q j j' hjj hj
    refine (h3 _ _).trans ?_
    simp only [Sum.elim_inr, ← Finset.mul_sum]
    have : ∀ l : Fin M, w (if (l : ℕ) < j then b q else a q) (if (l : ℕ) < j' then b q else a q) ≤
        (if (l : ℕ) < j' then w (a q) (b q) else 0) - if (l : ℕ) < j then w (a q) (b q) else 0 := by
      intro l
      split_ifs
      · rw [hw.self, sub_self]
      · omega
      · rw [sub_zero]
      · rw [hw.self, sub_self]
    have h4 := Finset.sum_le_sum fun l (_ : l ∈ univ) => this l
    rw [Finset.sum_sub_distrib, sum_lt hj, sum_lt (hjj.trans hj)] at h4
    refine (mul_le_mul_of_nonneg_left h4 (by positivity)).trans (le_of_eq ?_)
    field_simp
    ring
  · intro q j hj
    refine (h3 _ _).trans (le_of_eq ?_)
    simp only [Sum.elim_inl, Sum.elim_inr, id, ← Finset.mul_sum]
    have : ∀ l : Fin M, w (a q) (if (l : ℕ) < j then b q else a q) =
        if (l : ℕ) < j then w (a q) (b q) else 0 := by
      intro l
      split_ifs
      · rfl
      · exact hw.self _
    simp only [this, sum_lt hj]
    field_simp
    ring
  · intro q j hj
    refine (h3 _ _).trans (le_of_eq ?_)
    simp only [Sum.elim_inl, Sum.elim_inr, id, ← Finset.mul_sum]
    have : ∀ l : Fin M, w (b q) (if (l : ℕ) < j then b q else a q) =
        if (l : ℕ) < j then 0 else w (a q) (b q) := by
      intro l
      split_ifs
      · exact hw.self _
      · exact hw.symm _ _
    simp only [this, sum_lt hj]
    field_simp
    ring

/-! ### The fan -/

/-- The points of the fan: the old points, the points γ_i on both sheets, and the points G(i,j) on both sheets. -/
abbrev FanPts (Y : Type) : Type := (Y ⊕ (Bool × ℕ)) ⊕ ((Bool × ℕ) × ℕ)

namespace FanPts

/-- An old point. -/
def old (y : Y) : FanPts Y := Sum.inl (Sum.inl y)

/-- The point γ_i on the sheet b. -/
def γ (b : Bool) (i : ℕ) : FanPts Y := Sum.inl (Sum.inr (b, i))

/-- The point G(i,j) on the sheet b. -/
def G (b : Bool) (i j : ℕ) : FanPts Y := Sum.inr ((b, i), j)

end FanPts

open FanPts

/-- The fan for a given n, with θ = 1/T, L_i = |zγ_i| and ρ = 1 − jθ/n²: a price d on the old points, the γ_i and the
G(i,j) that extends w, with the four estimates of the paper,
"|γ_iγ_{i+1}| ≤ D/n², |zG(i,j)| = ρL_i, |G(i,j)G(i,j+1)| ≤ θL_i/n², |G(i,j)G(i+1,j)| ≤ ρD/n²",
and with what the text says on the places: γ_0 is at x (at v on the second sheet), γ_{n²} at m, |G(i,j)γ_i| ≤ (1−ρ)L_i, and
G(n²,j) "has distance 0 from its copy on the other sheet". -/
structure IsFan (K : Type) [Field K] (w : Y → Y → ℝ) (x : Bool → Y) (m z : Y) (D : ℝ) (T n : ℕ)
    (d : FanPts Y → FanPts Y → ℝ) : Prop where
  price : IsPrice K d
  old : ∀ a b, d (old a) (old b) = w a b
  γ_zero : ∀ b, d (γ b 0) (FanPts.old (x b)) = 0
  γ_last : ∀ b, d (γ b (n ^ 2)) (FanPts.old m) = 0
  γ_step : ∀ b i, i < n ^ 2 → d (γ b i) (γ b (i + 1)) ≤ D / n ^ 2
  z_G : ∀ b i j, j ≤ n ^ 2 * T → d (FanPts.old z) (G b i j) = (1 - j / (n ^ 2 * T)) * d (FanPts.old z) (γ b i)
  G_step_j : ∀ b i j, j < n ^ 2 * T → d (G b i j) (G b i (j + 1)) ≤ 1 / T * d (FanPts.old z) (γ b i) / n ^ 2
  G_step_i : ∀ b i j, i < n ^ 2 → j ≤ n ^ 2 * T → d (G b i j) (G b (i + 1) j) ≤ (1 - j / (n ^ 2 * T)) * D / n ^ 2
  G_γ : ∀ b i j, j ≤ n ^ 2 * T → d (G b i j) (γ b i) ≤ j / (n ^ 2 * T) * d (FanPts.old z) (γ b i)
  G_last : ∀ j, j ≤ n ^ 2 * T → d (G true (n ^ 2) j) (G false (n ^ 2) j) = 0

/-- **The fan** of the proof of Theorem thm:cn. "For a given n add, by Proposition prop:random, points γ_i, 0 ≤ i ≤ n²,
placed at m with probability i/n² and otherwise at x on the first sheet, at v on the second, with one random number for all.
Then, by the same proposition, add points G(i,j), 0 ≤ j ≤ Tn², placed at z with probability j/(Tn²) and otherwise at γ_i,
again with one random number." Then the four estimates hold. -/
theorem thm_cn_fan (hw : IsPrice K w) (x : Bool → Y) (m z : Y) {D : ℝ} (hD : ∀ b, w (x b) m ≤ D) {T n : ℕ}
    (hT : 0 < T) (hn : 0 < n) : ∃ d : FanPts Y → FanPts Y → ℝ, IsFan K w x m z D T n d := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hN : 0 < n ^ 2 := by positivity
  have hM : 0 < n ^ 2 * T := by positivity
  obtain ⟨w1, hw1, e1, -, a2, a3, a4⟩ := thm_cn_segments hw x (fun _ : Bool => m) hN
  obtain ⟨w2, hw2, e2, b1, b2, b3, b4⟩ := thm_cn_segments hw1
    (fun q : Bool × ℕ => (Sum.inr q : Y ⊕ (Bool × ℕ))) (fun _ => Sum.inl z) hM
  push_cast at a2 a3 a4 b1 b2 b3 b4
  have hx : ∀ b, w1 (Sum.inr (b, 0)) (Sum.inl (x b)) = 0 := by
    intro b
    have h := a3 b 0 (Nat.zero_le _)
    rw [Nat.cast_zero, zero_div, zero_mul] at h
    rw [hw1.symm]
    exact le_antisymm h (hw1.nonneg _ _)
  have hm : ∀ b, w1 (Sum.inr (b, n ^ 2)) (Sum.inl m) = 0 := by
    intro b
    have h := a4 b (n ^ 2) le_rfl
    push_cast at h
    rw [div_self (by positivity), sub_self, zero_mul] at h
    rw [hw1.symm]
    exact le_antisymm h (hw1.nonneg _ _)
  have hγ : ∀ b i, i < n ^ 2 → w1 (Sum.inr (b, i)) (Sum.inr (b, i + 1)) ≤ D / n ^ 2 := by
    intro b i hi
    have h := a2 b i (i + 1) (Nat.le_succ i) hi
    push_cast at h
    rw [add_sub_cancel_left, one_div_mul_eq_div] at h
    exact h.trans (div_le_div_of_nonneg_right (hD b) (by positivity))
  have hρ : ∀ j : ℕ, j ≤ n ^ 2 * T → 0 ≤ 1 - (j : ℝ) / (n ^ 2 * T) := by
    intro j hj
    rw [sub_nonneg, div_le_one (by positivity)]
    exact_mod_cast hj
  refine ⟨w2, hw2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    show w2 (Sum.inl (Sum.inl a)) (Sum.inl (Sum.inl b)) = w a b
    rw [e2, e1]
  · intro b
    show w2 (Sum.inl (Sum.inr (b, 0))) (Sum.inl (Sum.inl (x b))) = 0
    rw [e2, hx]
  · intro b
    show w2 (Sum.inl (Sum.inr (b, n ^ 2))) (Sum.inl (Sum.inl m)) = 0
    rw [e2, hm]
  · intro b i hi
    show w2 (Sum.inl (Sum.inr (b, i))) (Sum.inl (Sum.inr (b, i + 1))) ≤ D / n ^ 2
    rw [e2]
    exact hγ b i hi
  · intro b i j hj
    show w2 (Sum.inl (Sum.inl z)) (Sum.inr ((b, i), j)) =
      (1 - (j : ℝ) / (n ^ 2 * T)) * w2 (Sum.inl (Sum.inl z)) (Sum.inl (Sum.inr (b, i)))
    rw [e2, hw1.symm (Sum.inl z)]
    apply le_antisymm (b4 (b, i) j hj)
    have h1 := b3 (b, i) j hj
    have h2 := hw2.triangle (Sum.inl (Sum.inr (b, i))) (Sum.inr ((b, i), j)) (Sum.inl (Sum.inl z))
    rw [e2, hw2.symm (Sum.inr ((b, i), j))] at h2
    linarith
  · intro b i j hj
    show w2 (Sum.inr ((b, i), j)) (Sum.inr ((b, i), j + 1)) ≤
      1 / T * w2 (Sum.inl (Sum.inl z)) (Sum.inl (Sum.inr (b, i))) / n ^ 2
    rw [e2, hw1.symm (Sum.inl z)]
    have h := b2 (b, i) j (j + 1) (Nat.le_succ j) hj
    push_cast at h
    rw [add_sub_cancel_left] at h
    refine h.trans (le_of_eq ?_)
    field_simp
  · intro b i j hi hj
    show w2 (Sum.inr ((b, i), j)) (Sum.inr ((b, i + 1), j)) ≤ (1 - (j : ℝ) / (n ^ 2 * T)) * D / n ^ 2
    have h := b1 (b, i) (b, i + 1) j hj
    rw [hw1.self, mul_zero, add_zero] at h
    rw [mul_div_assoc]
    exact h.trans (mul_le_mul_of_nonneg_left (hγ b i hi) (hρ j hj))
  · intro b i j hj
    show w2 (Sum.inr ((b, i), j)) (Sum.inl (Sum.inr (b, i))) ≤
      (j : ℝ) / (n ^ 2 * T) * w2 (Sum.inl (Sum.inl z)) (Sum.inl (Sum.inr (b, i)))
    rw [e2, hw1.symm (Sum.inl z), hw2.symm]
    exact b3 (b, i) j hj
  · intro j hj
    show w2 (Sum.inr ((true, n ^ 2), j)) (Sum.inr ((false, n ^ 2), j)) = 0
    have h := b1 (true, n ^ 2) (false, n ^ 2) j hj
    have h7 : w1 (Sum.inr (true, n ^ 2)) (Sum.inr (false, n ^ 2)) = 0 := by
      rw [dist_congr_of_zero hw1 (hm true), hw1.symm]
      exact hm false
    rw [hw1.self, mul_zero, add_zero, h7, mul_zero] at h
    exact le_antisymm h (hw2.nonneg _ _)

/-! ### The fan in the coordinates of the windows -/

/-- "For (i,k) ∈ ℤ² on either sheet let P(i,k) = G(i′,j′), where i′ is i clamped to [0,n²] and j′ is i+k+n clamped to
[0,Tn²]". -/
def fanPt (T n : ℕ) (P : Bool × ℤ × ℤ) : FanPts Y :=
  G P.1 (cl (n ^ 2) P.2.1) (cl (n ^ 2 * T) (P.2.1 + P.2.2 + n))

/-- "… and let W_n be the pull-back of n² times the distance". -/
def fanDist (d : FanPts Y → FanPts Y → ℝ) (T n : ℕ) (P P' : Bool × ℤ × ℤ) : ℝ :=
  (n : ℝ) ^ 2 * d (fanPt T n P) (fanPt T n P')

/-- L_i = |zγ_i|, as a function on the sheets (i is clamped to [0,n²]). -/
def fanLen (d : FanPts Y → FanPts Y → ℝ) (z : Y) (n : ℕ) (b : Bool) (i : ℤ) : ℝ :=
  d (FanPts.old z) (γ b (cl (n ^ 2) i))

/-- The distance of P(i,k) from x, respectively v. -/
def fanPot (d : FanPts Y → FanPts Y → ℝ) (x : Bool → Y) (T n : ℕ) (b : Bool) (P : ℤ × ℤ) : ℝ :=
  d (FanPts.old (x b)) (fanPt T n (b, P))

theorem fanPt_mk (T n : ℕ) (b : Bool) (i k : ℤ) :
    (fanPt T n (b, (i, k)) : FanPts Y) = G b (cl (n ^ 2) i) (cl (n ^ 2 * T) (i + k + n)) := rfl

namespace IsFan

variable {x : Bool → Y} {m z : Y} {D : ℝ} {T n : ℕ} {d : FanPts Y → FanPts Y → ℝ}

theorem D_nonneg (F : IsFan K w x m z D T n d) (hn : 0 < n) : 0 ≤ D := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := (F.price.nonneg _ _).trans (F.γ_step true 0 (by positivity))
  have h2 := mul_nonneg h (sq_nonneg (n : ℝ))
  rwa [div_mul_cancel₀ _ (by positivity)] at h2

theorem γ_le (F : IsFan K w x m z D T n d) (hn : 0 < n) (b : Bool) (i i' : ℕ) (hi : i ≤ n ^ 2) (hi' : i' ≤ n ^ 2) :
    (n : ℝ) ^ 2 * d (γ b i) (γ b i') ≤ |(i : ℝ) - i'| * D := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := dist_chain_le F.price (γ b) (F.γ_step b) i i' hi hi'
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans (le_of_eq ?_)
  field_simp

theorem G_i_le (F : IsFan K w x m z D T n d) (hn : 0 < n) (b : Bool) (i i' j : ℕ) (hi : i ≤ n ^ 2) (hi' : i' ≤ n ^ 2)
    (hj : j ≤ n ^ 2 * T) :
    (n : ℝ) ^ 2 * d (G b i j) (G b i' j) ≤ (1 - j / (n ^ 2 * T)) * (|(i : ℝ) - i'| * D) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := dist_chain_le F.price (fun i => G b i j) (fun i hi => F.G_step_i b i j hi hj) i i' hi hi'
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans (le_of_eq ?_)
  field_simp

theorem G_j_le (F : IsFan K w x m z D T n d) (hn : 0 < n) (b : Bool) (i j j' : ℕ) (hj : j ≤ n ^ 2 * T)
    (hj' : j' ≤ n ^ 2 * T) :
    (n : ℝ) ^ 2 * d (G b i j) (G b i j') ≤ |(j : ℝ) - j'| / T * d (FanPts.old z) (γ b i) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := dist_chain_le F.price (G b i) (F.G_step_j b i) j j' hj hj'
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans (le_of_eq ?_)
  field_simp

theorem z_γ_last (F : IsFan K w x m z D T n d) (b : Bool) : d (FanPts.old z) (γ b (n ^ 2)) = w z m := by
  rw [F.price.symm, dist_congr_of_zero F.price (F.γ_last b), F.price.symm, F.old]

theorem z_γ_zero (F : IsFan K w x m z D T n d) (b : Bool) : d (FanPts.old z) (γ b 0) = w z (x b) := by
  rw [F.price.symm, dist_congr_of_zero F.price (F.γ_zero b), F.price.symm, F.old]

/-- "As L_i ≤ D + |zm| …" -/
theorem z_γ_le (F : IsFan K w x m z D T n d) (hn : 0 < n) (b : Bool) (i : ℕ) (hi : i ≤ n ^ 2) :
    d (FanPts.old z) (γ b i) ≤ D + w z m := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := F.price.triangle (FanPts.old z) (γ b (n ^ 2)) (γ b i)
  rw [F.z_γ_last] at h1
  have h3 := F.γ_le hn b (n ^ 2) i le_rfl hi
  have h4 : |((n ^ 2 : ℕ) : ℝ) - i| ≤ (n : ℝ) ^ 2 := by
    have : (i : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hi
    push_cast
    rw [abs_of_nonneg (by linarith)]
    linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have h5 := h3.trans (mul_le_mul_of_nonneg_right h4 (F.D_nonneg hn))
  have h6 := le_of_mul_le_mul_left h5 (by positivity)
  linarith

/-- W_n is a price on the two sheets. -/
theorem fanDist_price (F : IsFan K w x m z D T n d) : IsPrice K (fanDist d T n) :=
  (F.price.comp (fanPt T n)).smul (by positivity)

/-- "… we may take Λ = 2D + |zm|." -/
theorem lipschitz (F : IsFan K w x m z D T n d) (hT : 0 < T) (hn : 0 < n) (b : Bool) (P h : ℤ × ℤ) :
    fanDist d T n (b, P) (b, P + h) ≤ (2 * D + w z m) * (|(h.1 : ℝ)| + |(h.2 : ℝ)|) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hD0 := F.D_nonneg hn
  have h1 := F.price.triangle (fanPt T n (b, P))
    (G b (cl (n ^ 2) (P + h).1) (cl (n ^ 2 * T) (P.1 + P.2 + n))) (fanPt T n (b, P + h))
  have h2 := F.G_i_le hn b (cl (n ^ 2) P.1) (cl (n ^ 2) (P + h).1) (cl (n ^ 2 * T) (P.1 + P.2 + n))
    (cl_le _ _) (cl_le _ _) (cl_le _ _)
  have h3 := F.G_j_le hn b (cl (n ^ 2) (P + h).1) (cl (n ^ 2 * T) (P.1 + P.2 + n))
    (cl (n ^ 2 * T) ((P + h).1 + (P + h).2 + n)) (cl_le _ _) (cl_le _ _)
  have h4 := F.z_γ_le hn b (cl (n ^ 2) (P + h).1) (cl_le _ _)
  have h5 := cl_sub (n ^ 2) P.1 (P + h).1
  have h6 := cl_sub (n ^ 2 * T) (P.1 + P.2 + n) ((P + h).1 + (P + h).2 + n)
  have h7 : |(P.1 : ℝ) - (P + h).1| = |(h.1 : ℝ)| := by
    rw [Prod.fst_add]
    push_cast
    rw [sub_add_cancel_left, abs_neg]
  have h8 : |((P.1 + P.2 + n : ℤ) : ℝ) - ((P + h).1 + (P + h).2 + n : ℤ)| ≤ |(h.1 : ℝ)| + |(h.2 : ℝ)| := by
    rw [Prod.fst_add, Prod.snd_add]
    push_cast
    have : ((P.1 : ℝ) + P.2 + n) - (P.1 + h.1 + (P.2 + h.2) + n) = -((h.1 : ℝ) + h.2) := by ring
    rw [this, abs_neg]
    exact abs_add_le _ _
  rw [h7] at h5
  have h9 : (n : ℝ) ^ 2 * d (fanPt T n (b, P)) (G b (cl (n ^ 2) (P + h).1) (cl (n ^ 2 * T) (P.1 + P.2 + n))) ≤
      |(h.1 : ℝ)| * D := by
    refine h2.trans ?_
    have h10 : 0 ≤ ((cl (n ^ 2 * T) (P.1 + P.2 + n) : ℕ) : ℝ) / (n ^ 2 * T) := by positivity
    have h11 := mul_le_mul_of_nonneg_right h5 hD0
    have h12 : 0 ≤ |((cl (n ^ 2) P.1 : ℕ) : ℝ) - (cl (n ^ 2) (P + h).1 : ℕ)| * D :=
      mul_nonneg (abs_nonneg _) hD0
    nlinarith
  have h10 : (n : ℝ) ^ 2 * d (G b (cl (n ^ 2) (P + h).1) (cl (n ^ 2 * T) (P.1 + P.2 + n)))
      (fanPt T n (b, P + h)) ≤ (|(h.1 : ℝ)| + |(h.2 : ℝ)|) * (D + w z m) := by
    refine h3.trans (mul_le_mul ?_ h4 (F.price.nonneg _ _) (by positivity))
    exact (div_le_self (abs_nonneg _) hT1).trans (h6.trans h8)
  have h11 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (n : ℝ) ^ 2 by positivity)
  rw [mul_add] at h11
  have h12 : 0 ≤ |(h.2 : ℝ)| * D := by positivity
  unfold fanDist
  linarith

/-- A step in the direction (1,−1) "changes i only": it has length at most ρD. -/
theorem step_ii (F : IsFan K w x m z D T n d) (hT : 0 < T) (hn : 0 < n) (b : Bool) (i k : ℤ) (h0 : 0 ≤ i + k + n)
    (h1 : i + k + n ≤ n ^ 2 * T) :
    fanDist d T n (b, (i, k)) (b, (i + 1, k - 1)) ≤ (1 - (i + k + n) / (n ^ 2 * T)) * D := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have e : i + 1 + (k - 1) + n = i + k + n := by ring
  have h6 := F.G_i_le hn b (cl (n ^ 2) i) (cl (n ^ 2) (i + 1)) (cl (n ^ 2 * T) (i + k + n)) (cl_le _ _)
    (cl_le _ _) (cl_le _ _)
  rw [cl_window h0 h1] at h6
  rw [fanDist, fanPt_mk, fanPt_mk, e]
  refine h6.trans ?_
  have h7 : ((i : ℝ) + k + n) ≤ n ^ 2 * T := by exact_mod_cast h1
  have h8 : 0 ≤ 1 - ((i : ℝ) + k + n) / (n ^ 2 * T) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact h7
  apply mul_le_mul_of_nonneg_left _ h8
  calc _ ≤ 1 * D := mul_le_mul_of_nonneg_right (cl_succ _ i) (F.D_nonneg hn)
    _ = D := one_mul D

/-- "The distance from z gives" a lower bound for W_n: n²(ρL_i − ρ′L_i′) ≤ W_n(P(i,k), P(i′,k′)). -/
theorem from_z (F : IsFan K w x m z D T n d) (b : Bool) (i k i' k' : ℤ) (h0 : 0 ≤ i + k + n)
    (h1 : i + k + n ≤ n ^ 2 * T) (h0' : 0 ≤ i' + k' + n) (h1' : i' + k' + n ≤ n ^ 2 * T) :
    (n : ℝ) ^ 2 * ((1 - (i + k + n) / (n ^ 2 * T)) * fanLen d z n b i
      - (1 - (i' + k' + n) / (n ^ 2 * T)) * fanLen d z n b i') ≤ fanDist d T n (b, (i, k)) (b, (i', k')) := by
  have h6 := F.price.triangle (FanPts.old z) (fanPt T n (b, (i', k'))) (fanPt T n (b, (i, k)))
  rw [fanPt_mk, fanPt_mk, F.z_G _ _ _ (cl_le _ _), F.z_G _ _ _ (cl_le _ _), cl_window h0 h1,
    cl_window h0' h1'] at h6
  rw [fanDist, fanLen, fanLen, fanPt_mk, fanPt_mk, F.price.symm (G b (cl (n ^ 2) i) (cl (n ^ 2 * T) (i + k + n)))
    (G b (cl (n ^ 2) i') (cl (n ^ 2 * T) (i' + k' + n)))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

/-- A step in the direction (0,1) has length at most θL_i. -/
theorem step_iii (F : IsFan K w x m z D T n d) (hn : 0 < n) (b : Bool) (i k : ℤ) (h0 : 0 ≤ i + k + n)
    (h1 : i + k + 1 + n ≤ n ^ 2 * T) :
    fanDist d T n (b, (i, k)) (b, (i, k + 1)) ≤ fanLen d z n b i / T := by
  have e : i + (k + 1) + n = i + k + 1 + n := by ring
  have h6 := F.G_j_le hn b (cl (n ^ 2) i) (cl (n ^ 2 * T) (i + k + n)) (cl (n ^ 2 * T) (i + (k + 1) + n))
    (cl_le _ _) (cl_le _ _)
  rw [cl_window h0 (by linarith), cl_window (by rw [e]; linarith) (by rw [e]; exact h1)] at h6
  rw [fanDist, fanLen, fanPt_mk, fanPt_mk]
  refine h6.trans (le_of_eq ?_)
  push_cast
  have : (i : ℝ) + k + n - (i + (k + 1) + n) = -1 := by ring
  rw [this, abs_neg, abs_one]
  ring

theorem fanLen_zero (F : IsFan K w x m z D T n d) (b : Bool) : fanLen d z n b 0 = w z (x b) := by
  rw [fanLen, cl_zero, F.z_γ_zero]

theorem fanLen_last (F : IsFan K w x m z D T n d) (b : Bool) : fanLen d z n b (n ^ 2) = w z m := by
  rw [fanLen, cl_sq, F.z_γ_last]

theorem fanLen_nonneg (F : IsFan K w x m z D T n d) (b : Bool) (i : ℤ) : 0 ≤ fanLen d z n b i :=
  F.price.nonneg _ _

theorem fanLen_le (F : IsFan K w x m z D T n d) (hn : 0 < n) (b : Bool) (i : ℤ) : fanLen d z n b i ≤ D + w z m :=
  F.z_γ_le hn b _ (cl_le _ _)

theorem fanLen_step (F : IsFan K w x m z D T n d) (hn : 0 < n) (b : Bool) (i : ℤ) :
    |(n : ℝ) ^ 2 * (fanLen d z n b (i + 1) - fanLen d z n b i)| ≤ D := by
  have h1 := F.γ_le hn b (cl (n ^ 2) i) (cl (n ^ 2) (i + 1)) (cl_le _ _) (cl_le _ _)
  have h2 : |((cl (n ^ 2) i : ℕ) : ℝ) - (cl (n ^ 2) (i + 1) : ℕ)| * D ≤ D := by
    calc _ ≤ 1 * D := mul_le_mul_of_nonneg_right (cl_succ _ i) (F.D_nonneg hn)
      _ = D := one_mul D
  have h3 := F.price.triangle (FanPts.old z) (γ b (cl (n ^ 2) i)) (γ b (cl (n ^ 2) (i + 1)))
  have h4 := F.price.triangle (FanPts.old z) (γ b (cl (n ^ 2) (i + 1))) (γ b (cl (n ^ 2) i))
  rw [F.price.symm (γ b (cl (n ^ 2) (i + 1))) (γ b (cl (n ^ 2) i))] at h4
  have h5 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  unfold fanLen
  rw [abs_le]
  constructor <;> nlinarith

theorem fanPot_sub_le (F : IsFan K w x m z D T n d) (b : Bool) (P P' : ℤ × ℤ) :
    (n : ℝ) ^ 2 * (fanPot d x T n b P - fanPot d x T n b P') ≤ fanDist d T n (b, P) (b, P') := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have := F.price.triangle (FanPts.old (x b)) (fanPt T n (b, P')) (fanPt T n (b, P))
  rw [F.price.symm (fanPt T n (b, P')) (fanPt T n (b, P))] at this
  unfold fanPot
  linarith

/-- "Steps in the direction (1,0) lead to a common end": the two ends have distance 0, so their distances from x and v add
up to at least |xv|. -/
theorem fanPot_last (F : IsFan K w x m z D T n d) (k : ℤ) :
    w (x true) (x false) ≤ fanPot d x T n true (n ^ 2, k) + fanPot d x T n false (n ^ 2, k) := by
  rw [fanPot, fanPot, fanPt_mk, fanPt_mk, cl_sq]
  have h10 := F.price.triangle (FanPts.old (x true)) (G true (n ^ 2) (cl (n ^ 2 * T) ((n : ℤ) ^ 2 + k + n)))
    (FanPts.old (x false))
  rw [F.old, dist_congr_of_zero F.price (F.G_last _ (cl_le _ _)), F.price.symm (G false _ _)] at h10
  exact h10

/-- The steps in the direction (1,0) start "from a point within O(1/n) of x, respectively v". -/
theorem fanPot_zero (F : IsFan K w x m z D T n d) (b : Bool) (k : ℤ) (h0 : 0 ≤ k + n) (h1 : k + n ≤ n ^ 2 * T) :
    fanPot d x T n b (0, k) ≤ (k + n) / (n ^ 2 * T) * w z (x b) := by
  have h6 := F.G_γ b 0 _ (cl_le (n ^ 2 * T) (0 + k + n))
  rw [cl_window (by linarith) (by linarith), F.z_γ_zero] at h6
  have h8 : d (FanPts.old (x b)) (γ b 0) = 0 := by rw [F.price.symm, F.γ_zero]
  rw [fanPot, fanPt_mk, cl_zero, dist_congr_of_zero F.price h8, F.price.symm]
  refine h6.trans (le_of_eq ?_)
  push_cast
  ring

end IsFan

/-- The display of claim (iv): "Let L′ = L_{i+S}, L = L_i; for n ≥ AS the new j is not negative. The distance from z gives
W(P, P + S(1,−1−A)) ≥ |n²ρ(L′ − L) + ASθL′|." Here P = P(i,k), j = i + k + n ≥ AS, ρ = 1 − jθ/n² and θ = 1/T. -/
theorem thm_cn_iv_step {x : Bool → Y} {m z : Y} {D : ℝ} {T n : ℕ} {d : FanPts Y → FanPts Y → ℝ}
    (F : IsFan K w x m z D T n d) (hT : 0 < T) (hn : 0 < n) (b : Bool) (i k : ℤ) (A S : ℕ)
    (h0 : ((A * S : ℕ) : ℤ) ≤ i + k + n) (h1 : i + k + n ≤ n ^ 2 * T) :
    |(n : ℝ) ^ 2 * ((1 - (i + k + n) / (n ^ 2 * T)) * (fanLen d z n b (i + S) - fanLen d z n b i))
        + A * S * (1 / T) * fanLen d z n b (i + S)| ≤
      fanDist d T n (b, (i, k)) (b, (i + S, k - S - (A * S : ℕ))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have k0 : 0 ≤ i + k + n := le_trans (Int.natCast_nonneg _) h0
  have k2 : (0 : ℤ) ≤ (i + S) + (k - S - (A * S : ℕ)) + n := by linarith
  have k3 : (i + S) + (k - S - (A * S : ℕ)) + n ≤ n ^ 2 * T := by linarith [Int.natCast_nonneg (A * S)]
  have g1 := F.from_z b (i + S) (k - S - (A * S : ℕ)) i k k2 k3 k0 h1
  have g2 := F.from_z b i k (i + S) (k - S - (A * S : ℕ)) k0 h1 k2 k3
  rw [F.fanDist_price.symm] at g1
  push_cast at g1 g2
  have e1 : 1 - ((i : ℝ) + S + (k - S - A * S) + n) / (n ^ 2 * T) =
      1 - (i + k + n) / (n ^ 2 * T) + A * S / (n ^ 2 * T) := by ring
  have e2 : (n : ℝ) ^ 2 * (A * S / (n ^ 2 * T)) = A * S * (1 / T) := by field_simp
  rw [e1] at g1 g2
  rw [abs_le, ← e2]
  constructor
  · refine le_trans (neg_le_neg g2) (le_of_eq ?_)
    ring
  · refine le_trans (le_of_eq ?_) g1
    ring

/-! ### The sequence of fans and its seminorm

Above, fanDist, fanLen and fanPot belong to one fan, for one n. From here on d n is a fan for every n, and fanW (fanWs on one
sheet), fanL and fanP are the corresponding sequences: the paper's W = (W_n), L = (L_i), and the distances from x and v. -/

section Claims

variable {x : Bool → Y} {m z : Y} {D : ℝ} {T : ℕ} {d : ℕ → FanPts Y → FanPts Y → ℝ}

/-- The sequence W = (W_n) of the fans d n. (The window for n = 0 is empty; there the fan for n = 1 is used.) -/
def fanW (d : ℕ → FanPts Y → FanPts Y → ℝ) (T n : ℕ) : Bool × ℤ × ℤ → Bool × ℤ × ℤ → ℝ :=
  fanDist (d n) T (max n 1)

/-- W on each sheet. -/
def fanWs (d : ℕ → FanPts Y → FanPts Y → ℝ) (T n : ℕ) (b : Bool) (P P' : ℤ × ℤ) : ℝ := fanW d T n (b, P) (b, P')

/-- The sequence L = (L_i). -/
def fanL (d : ℕ → FanPts Y → FanPts Y → ℝ) (z : Y) (n : ℕ) (b : Bool) (i : ℤ) : ℝ := fanLen (d n) z (max n 1) b i

/-- The distances from x, respectively v. -/
def fanP (d : ℕ → FanPts Y → FanPts Y → ℝ) (x : Bool → Y) (T n : ℕ) (b : Bool) (P : ℤ × ℤ) : ℝ :=
  fanPot (d n) x T (max n 1) b P

/-- "Let Λ₂ = E L², over both sheets". -/
noncomputable def fanΛ₂ (d : ℕ → FanPts Y → FanPts Y → ℝ) (z : Y) : ℝ :=
  mean ((fun n b i _ => fanL d z n b i : Fn) * (fun n b i _ => fanL d z n b i : Fn))

theorem fanW_price (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (n : ℕ) : IsPrice K (fanW d T n) :=
  (hd n).fanDist_price

/-- "As L_i ≤ D + |zm|, we may take Λ = 2D + |zm|." -/
theorem thm_cn_lipschitz (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 0 < T) (n : ℕ) (b : Bool)
    (P g : ℤ × ℤ) : fanW d T n (b, P) (b, P + g) ≤ (2 * D + w z m) * (|(g.1 : ℝ)| + |(g.2 : ℝ)|) :=
  (hd n).lipschitz hT (max_one_pos n) b P g

theorem fanWs_lip (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 0 < T) :
    Lip (fanWs d T) (2 * D + w z m) :=
  lem_means_lip (fanW_price hd) (thm_cn_lipschitz hd hT)

theorem fan_w_nonneg (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (a b : Y) : 0 ≤ w a b := by
  rw [← (hd 0).old]
  exact (hd 0).price.nonneg _ _

theorem fan_D_nonneg (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) : 0 ≤ D := (hd 0).D_nonneg (max_one_pos 0)

theorem fanP_sub_le (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (n : ℕ) (b : Bool) (P P' : ℤ × ℤ) :
    (n : ℝ) ^ 2 * (fanP d x T n b P - fanP d x T n b P') ≤ fanWs d T n b P P' := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : 0 ≤ fanWs d T 0 b P P' := (fanW_price hd 0).nonneg (b, P) (b, P')
    simpa using h0
  · have : ((max n 1 : ℕ) : ℝ) ^ 2 * (fanP d x T n b P - fanP d x T n b P') ≤ fanWs d T n b P P' :=
      (hd n).fanPot_sub_le b P P'
    rwa [max_eq_left hn] at this

theorem fanL_step (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (n : ℕ) (b : Bool) (i : ℤ) :
    |(n : ℝ) ^ 2 * (fanL d z n b (i + 1) - fanL d z n b i)| ≤ D := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using fan_D_nonneg hd
  · have : |((max n 1 : ℕ) : ℝ) ^ 2 * (fanL d z n b (i + 1) - fanL d z n b i)| ≤ D :=
      (hd n).fanLen_step (max_one_pos n) b i
    rwa [max_eq_left hn] at this

theorem fanL_nonneg (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (n : ℕ) (b : Bool) (i : ℤ) :
    0 ≤ fanL d z n b i := (hd n).fanLen_nonneg b i

theorem fanL_le (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (n : ℕ) (b : Bool) (i : ℤ) :
    fanL d z n b i ≤ D + w z m := (hd n).fanLen_le (max_one_pos n) b i

theorem fanL_bd (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) : Bd fun n b i _ => fanL d z n b i := by
  refine ⟨D + w z m, fun n b i k => ?_⟩
  rw [abs_of_nonneg (fanL_nonneg hd n b i)]
  exact fanL_le hd n b i

/-- "… so Λ₂ ≤ (D + |zm|)²". -/
theorem thm_cn_Λ₂_le (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) : fanΛ₂ d z ≤ (D + w z m) ^ 2 := by
  have h1 := mean_le ((fanL_bd hd).mul (fanL_bd hd)) (Bd.const ((D + w z m) ^ 2)) (fun n b i k => by
    simp only [Pi.mul_apply]
    rw [sq]
    exact mul_self_le_mul_self (fanL_nonneg hd n b i) (fanL_le hd n b i))
  rwa [mean_const] at h1

/-- **Claim (i)** of the proof of Theorem thm:cn: "N(1,0) ≥ D". -/
theorem thm_cn_i (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 2 ≤ T)
    (hxx : w (x true) (x false) = 2 * D) : D ≤ meanNorm (fanW d T) (1, 0) := by
  have hT0 : 0 < T := by omega
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT0
  have H := fanWs_lip hd hT0
  have hX : Bd fun n b i k => (n : ℝ) ^ 2 * (fanP d x T n b (i + 1, k) - fanP d x T n b (i, k)) := by
    refine ⟨2 * D + w z m, fun n b i k => ?_⟩
    have h1 := H.lip n b (i, k) (1, 0)
    rw [prod_add_mk] at h1
    simp only [Int.cast_one, abs_one, Int.cast_zero, abs_zero, add_zero, mul_one] at h1
    have h2 := fanP_sub_le hd n b (i + 1, k) (i, k)
    have h3 := fanP_sub_le hd n b (i, k) (i + 1, k)
    rw [H.symm] at h2
    rw [abs_le]
    constructor <;> linarith
  have h1 : Tendsto (fun n : ℕ => 2 * D - 2 * (w z (x true) + w z (x false)) / T * (1 / (n : ℝ)))
      atTop (𝓝 (2 * D - 2 * (w z (x true) + w z (x false)) / T * 0)) :=
    (tendsto_one_div_atTop_nhds_zero_nat.const_mul _).const_sub _
  rw [mul_zero, sub_zero] at h1
  have h2 := le_mean_tele (F := fun n b i k => fanP d x T n b (i, k)) hX h1 (by
    filter_upwards [eventually_large hT 0] with n hnn k hk
    obtain ⟨e, hn1, -, hn2, -⟩ := hnn
    have g1 : w (x true) (x false) ≤ fanP d x T n true (((max n 1 : ℕ) : ℤ) ^ 2, k)
        + fanP d x T n false (((max n 1 : ℕ) : ℤ) ^ 2, k) := (hd n).fanPot_last (k : ℤ)
    have g2 : _ → _ → fanP d x T n true (0, k) ≤ _ := (hd n).fanPot_zero true (k : ℤ)
    have g3 : _ → _ → fanP d x T n false (0, k) ≤ _ := (hd n).fanPot_zero false (k : ℤ)
    rw [e] at g1 g2 g3
    have k2 : (k : ℤ) + n ≤ n ^ 2 * T := by
      have : k + n ≤ n ^ 2 * T := by omega
      exact_mod_cast this
    have g2 := g2 (by positivity) k2
    have g3 := g3 (by positivity) k2
    rw [Fintype.sum_bool]
    push_cast at g1 g2 g3 ⊢
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk.le
    have g4 : ((k : ℝ) + n) / (n ^ 2 * T) ≤ 2 / T * (1 / n) := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ T by positivity) (show (0 : ℝ) ≤ n by positivity)]
    have w1 := mul_le_mul_of_nonneg_right g4 (fan_w_nonneg hd z (x true))
    have w2 := mul_le_mul_of_nonneg_right g4 (fan_w_nonneg hd z (x false))
    have e2 : 2 * (w z (x true) + w z (x false)) / T * (1 / (n : ℝ)) =
        2 / T * (1 / n) * w z (x true) + 2 / T * (1 / n) * w z (x false) := by ring
    rw [e2]
    linarith)
  apply le_meanNorm
  intro S hS
  obtain ⟨h3, h4⟩ := mean_steps (F := fun n b i k => fanP d x T n b (i, k)) hX S
  have h5 : mean (fun n b i k => (n : ℝ) ^ 2 * (fanP d x T n b (i + S, k) - fanP d x T n b (i, k))) ≤
      mean (df (fanWs d T) 0 (S • (1, 0))) := by
    apply mean_le h3 (H.bd _ _)
    intro n b i k
    have h6 := fanP_sub_le hd n b (i + S, k) (i, k)
    rw [H.symm] at h6
    simpa [df, prod_add_mk] using h6
  have h6 := mean_le_nm (H.bd 0 (S • (1, 0)))
  have h7 : (S : ℝ) * D ≤
      S * mean (fun n b i k => (n : ℝ) ^ 2 * (fanP d x T n b (i + 1, k) - fanP d x T n b (i, k))) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg S)
    linarith
  rw [mul_comm]
  exact (h7.trans (h4.symm.le.trans h5)).trans h6

/-- **Claim (ii)** of the proof of Theorem thm:cn: "N(1,−1)² ≤ D²(1 − θ + θ²)". -/
theorem thm_cn_ii (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 2 ≤ T) :
    meanNorm (fanW d T) (1, -1) ^ 2 ≤ D ^ 2 * (1 - 1 / T + (1 / T : ℝ) ^ 2) := by
  have hT0 : 0 < T := by omega
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT0
  have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hD0 := fan_D_nonneg hd
  have H := fanWs_lip hd hT0
  set θ : ℝ := 1 / T with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hT']
    linarith
  have hpos : ∀ n b i k, 0 ≤ 1 - θ * place n b i k := by
    intro n b i k
    have h1 := place_nonneg n b i k
    have h2 := place_le_one n b i k
    nlinarith
  have hg : Bd fun n b i k => D * (1 - θ * place n b i k) := by
    refine ⟨D, fun n b i k => ?_⟩
    rw [abs_of_nonneg (mul_nonneg hD0 (hpos n b i k))]
    have := mul_nonneg hθ0.le (place_nonneg n b i k)
    nlinarith
  have h1 : meanLength (fanW d T) (1, -1) ≤ nm fun n b i k => D * (1 - θ * place n b i k) := by
    apply nm_mono (H.bd _ _) hg (fun n b i k => H.nonneg _ _ _ _)
    filter_upwards [eventually_large hT 0] with n hnn b i hi k hk
    obtain ⟨e, hn1, -, hn2, -⟩ := hnn
    have g : _ → _ → fanWs d T n b (i, k) (i + 1, k - 1) ≤ _ := (hd n).step_ii hT0 (max_one_pos n) b i k
    rw [e] at g
    have k1 : (i : ℤ) + k + n ≤ n ^ 2 * T := by
      have : i + k + n ≤ n ^ 2 * T := by omega
      exact_mod_cast this
    have g := g (by positivity) k1
    push_cast at g
    have h2 : df (fanWs d T) 0 (1, -1) n b i k = fanWs d T n b (i, k) (i + 1, k - 1) := by
      simp [df, sub_eq_add_neg]
    rw [h2]
    refine g.trans ?_
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hD0
    have h3 : place n b i k = (i : ℝ) / n ^ 2 := by
      rw [place, cl_cast (Int.natCast_nonneg i) (by exact_mod_cast hi.le)]
      push_cast
      rfl
    have h4 : θ * ((i : ℝ) / n ^ 2) = i / (n ^ 2 * T) := by rw [hθ]; field_simp
    rw [h3, h4]
    have h5 : (i : ℝ) / (n ^ 2 * T) ≤ (i + k + n) / (n ^ 2 * T) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    linarith
  have h2 : nm (fun n b i k => D * (1 - θ * place n b i k)) ^ 2 ≤ D ^ 2 * (1 - θ + θ ^ 2) := by
    rw [nm_sq hg]
    have h3 : mean ((fun n b i k => D * (1 - θ * place n b i k)) *
        fun n b i k => D * (1 - θ * place n b i k)) ≤
        mean ((fun _ _ _ _ => D ^ 2 * (1 + θ ^ 2)) + (-(2 * θ * D ^ 2)) • place) := by
      apply mean_le (hg.mul hg) ((Bd.const _).add (bd_place.smul _))
      intro n b i k
      simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := place_nonneg n b i k
      have h2 := place_le_one n b i k
      have h4 : θ ^ 2 * D ^ 2 * place n b i k ^ 2 ≤ θ ^ 2 * D ^ 2 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      nlinarith
    rw [mean_add (Bd.const _) (bd_place.smul _), mean_const, mean_smul bd_place, mean_place] at h3
    linarith
  have h3 := (meanNorm_le_meanLength (fanW d T) (1, -1)).trans h1
  exact (pow_le_pow_left₀ (meanNorm_nonneg _ _) h3 2).trans h2

/-- **Claim (iii)** of the proof of Theorem thm:cn: "N(0,1)² ≤ θ²Λ₂". -/
theorem thm_cn_iii (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 2 ≤ T) :
    meanNorm (fanW d T) (0, 1) ^ 2 ≤ (1 / T : ℝ) ^ 2 * fanΛ₂ d z := by
  have hT0 : 0 < T := by omega
  have H := fanWs_lip hd hT0
  have hLf := fanL_bd hd
  set θ : ℝ := 1 / T with hθ
  have h1 : meanLength (fanW d T) (0, 1) ≤ nm (θ • (fun n b i _ => fanL d z n b i : Fn)) := by
    apply nm_mono (H.bd _ _) (hLf.smul θ) (fun n b i k => H.nonneg _ _ _ _)
    filter_upwards [eventually_large hT 1] with n hnn b i hi k hk
    obtain ⟨e, hn1, hn3, hn2, -⟩ := hnn
    have g : _ → _ → fanWs d T n b (i, k) (i, k + 1) ≤ fanL d z n b i / T :=
      (hd n).step_iii (max_one_pos n) b i k
    rw [e] at g
    have k1 : (i : ℤ) + k + 1 + n ≤ n ^ 2 * T := by
      have : i + k + 1 + n ≤ n ^ 2 * T := by omega
      exact_mod_cast this
    have g := g (by positivity) k1
    have h2 : df (fanWs d T) 0 (0, 1) n b i k = fanWs d T n b (i, k) (i, k + 1) := by simp [df]
    rw [h2]
    refine g.trans (le_of_eq ?_)
    simp only [Pi.smul_apply, smul_eq_mul, hθ]
    ring
  have h2 : nm (θ • (fun n b i _ => fanL d z n b i : Fn)) ^ 2 = θ ^ 2 * fanΛ₂ d z := by
    rw [nm_sq (hLf.smul θ)]
    have : (θ • (fun n b i _ => fanL d z n b i : Fn) : Fn) * (θ • (fun n b i _ => fanL d z n b i : Fn)) =
        (θ ^ 2) • ((fun n b i _ => fanL d z n b i : Fn) * (fun n b i _ => fanL d z n b i : Fn)) := by
      funext n b i k
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this, mean_smul (hLf.mul hLf), fanΛ₂]
  rw [← h2]
  exact pow_le_pow_left₀ (meanNorm_nonneg _ _) ((meanNorm_le_meanLength _ _).trans h1) 2

/-- "n²|L′² − L²| ≤ 2SD(D + |zm|)", for L′ = L_{i+S} and L = L_i. -/
theorem thm_cn_iv_bound (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (n : ℕ) (b : Bool) (i : ℤ) (S : ℕ) :
    |(n : ℝ) ^ 2 * (fanL d z n b (i + S) ^ 2 - fanL d z n b i ^ 2)| ≤ 2 * (D + w z m) * (S * D) := by
  have hD0 := fan_D_nonneg hd
  have hB0 := fan_w_nonneg hd z m
  have hLs : ∀ S : ℕ, |(n : ℝ) ^ 2 * (fanL d z n b (i + S) - fanL d z n b i)| ≤ S * D := by
    intro S
    induction S with
    | zero => simp
    | succ S ih =>
      have h1 := fanL_step hd n b (i + S)
      have e : (n : ℝ) ^ 2 * (fanL d z n b (i + (S + 1 : ℕ)) - fanL d z n b i) =
          n ^ 2 * (fanL d z n b (i + S + 1) - fanL d z n b (i + S))
            + n ^ 2 * (fanL d z n b (i + S) - fanL d z n b i) := by
        push_cast
        rw [← add_assoc]
        ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      push_cast
      linarith
  have e : (n : ℝ) ^ 2 * (fanL d z n b (i + S) ^ 2 - fanL d z n b i ^ 2) =
      (fanL d z n b (i + S) + fanL d z n b i) * (n ^ 2 * (fanL d z n b (i + S) - fanL d z n b i)) := by ring
  rw [e, abs_mul]
  apply mul_le_mul _ (hLs S) (abs_nonneg _) (by positivity)
  rw [abs_of_nonneg (add_nonneg (fanL_nonneg hd n b _) (fanL_nonneg hd n b _))]
  linarith [fanL_le hd n b (i + S), fanL_le hd n b i]

theorem fanL_sq_bd (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) :
    Bd fun n b i _ => (n : ℝ) ^ 2 * (fanL d z n b (i + 1) ^ 2 - fanL d z n b i ^ 2) :=
  ⟨2 * (D + w z m) * ((1 : ℕ) * D), fun n b i _ => by simpa using thm_cn_iv_bound hd n b i 1⟩

/-- "n²(L′² − L²) telescopes along i to the mean SΓ", with Γ = |mz|² − ½|xz|² − ½|vz|²: here for S = 1, and only that the mean
is at least Γ, which is what claim (iv) uses. (Cat.mean_steps passes from S = 1 to any S.) -/
theorem thm_cn_iv_telescope (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 2 ≤ T) :
    w z m ^ 2 - (w z (x true) ^ 2 + w z (x false) ^ 2) / 2 ≤
      mean (fun n b i _ => (n : ℝ) ^ 2 * (fanL d z n b (i + 1) ^ 2 - fanL d z n b i ^ 2)) := by
  have h := le_mean_tele (F := fun n b i _ => fanL d z n b i ^ 2) (fanL_sq_bd hd)
    (c := fun _ => 2 * (w z m ^ 2 - (w z (x true) ^ 2 + w z (x false) ^ 2) / 2)) tendsto_const_nhds (by
      filter_upwards [eventually_large hT 0] with n hnn k hk
      obtain ⟨e, -⟩ := hnn
      have g1 : fanL d z n true (((max n 1 : ℕ) : ℤ) ^ 2) = w z m := (hd n).fanLen_last true
      have g2 : fanL d z n false (((max n 1 : ℕ) : ℤ) ^ 2) = w z m := (hd n).fanLen_last false
      have g3 : fanL d z n true 0 = w z (x true) := (hd n).fanLen_zero true
      have g4 : fanL d z n false 0 = w z (x false) := (hd n).fanLen_zero false
      rw [e] at g1 g2
      rw [Fintype.sum_bool, g3, g4]
      push_cast
      rw [g1, g2]
      linarith)
  linarith

/-- The next sentence of claim (iv): "Square this, use 2L′(L′ − L) ≥ L′² − L², and note that … 1 − ρ ≤ 2θ … and
n²|L′² − L²| ≤ 2SD(D + |zm|)." So for large n, at the points P = P(i,k) of the window,
W(P, P + S(1,−1−A))² ≥ (ASθ)²L′² + ASθ·n²(L′² − L²) − 4Aθ²S²D(D + |zm|). -/
theorem thm_cn_iv_square (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 2 ≤ T) (A S : ℕ) {n : ℕ}
    (hnn : max n 1 = n ∧ (1 : ℝ) ≤ n ∧ A * S ≤ n ∧ n ^ 2 + 2 * n ≤ n ^ 2 * T ∧ n ^ 2 + 2 * n ≤ 2 * n ^ 2)
    (b : Bool) {i k : ℕ} (hi : i < n ^ 2) (hk : k < n) :
    (A * S * (1 / T : ℝ)) ^ 2 * (fanL d z n b (i + S) * fanL d z n b (i + S))
      + A * S * (1 / T : ℝ) * ((n : ℝ) ^ 2 * (fanL d z n b (i + S) ^ 2 - fanL d z n b i ^ 2))
      - 4 * A * (1 / T : ℝ) ^ 2 * S ^ 2 * D * (D + w z m) ≤
      fanWs d T n b (i, k) (i + S, k - S - (A * S : ℕ)) * fanWs d T n b (i, k) (i + S, k - S - (A * S : ℕ)) := by
  obtain ⟨e, hn1, hAS, hn2, hn3⟩ := hnn
  have hT' : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hn0 : (0 : ℝ) < n := by linarith
  have hD0 := fan_D_nonneg hd
  have hB0 := fan_w_nonneg hd z m
  have k0 : ((A * S : ℕ) : ℤ) ≤ (i : ℤ) + k + n := by
    have : ((A * S : ℕ) : ℤ) ≤ n := by exact_mod_cast hAS
    linarith [Int.natCast_nonneg i, Int.natCast_nonneg k]
  have k1 : (i : ℤ) + k + n ≤ n ^ 2 * T := by
    have : i + k + n ≤ n ^ 2 * T := by omega
    exact_mod_cast this
  have g : _ → _ → |((max n 1 : ℕ) : ℝ) ^ 2 * (_ * (fanL d z n b (i + S) - fanL d z n b i))
      + A * S * (1 / T) * fanL d z n b (i + S)| ≤ fanWs d T n b (i, k) (i + S, k - S - (A * S : ℕ)) :=
    thm_cn_iv_step (hd n) (by omega) (max_one_pos n) b i k A S
  rw [e] at g
  have g := abs_le.1 (g k0 k1)
  push_cast at g
  set r : ℝ := 1 - (i + k + n) / (n ^ 2 * T) with hr
  have hr0 : 0 ≤ r := by
    rw [hr, sub_nonneg, div_le_one (by positivity)]
    exact_mod_cast k1
  have hr1 : 1 - r ≤ 2 * (1 / T) := by
    rw [hr, sub_sub_cancel, div_le_iff₀ (by positivity)]
    have k4 : (i : ℝ) + k + n ≤ 2 * n ^ 2 := by
      have : i + k + n ≤ 2 * n ^ 2 := by omega
      exact_mod_cast this
    refine k4.trans (le_of_eq ?_)
    field_simp
  have hr2 : 0 ≤ 1 - r := by
    rw [hr, sub_sub_cancel]
    positivity
  have E4 := sq_core hr0 hr2 hr1 (a := A * S * (1 / T)) (by positivity)
    (show 0 ≤ 2 * (D + w z m) * (S * D) by positivity) (abs_le.1 (thm_cn_iv_bound hd n b i S)).2
    (W := fanWs d T n b (i, k) (i + S, k - S - (A * S : ℕ)))
    (le_trans (le_of_eq (by ring)) g.2) (le_trans (le_of_eq (by ring)) (neg_le.1 g.1))
  refine le_trans (le_of_eq ?_) E4
  ring

/-- The end of claim (iv), for ν: "n²(L′² − L²) telescopes along i to the mean SΓ, while … the mean of L′² is Λ₂": so
ν(S(1,−1−A))² ≥ S²(A²θ²Λ₂ + AθΓ − 4Aθ²D(D + |zm|)) for every S. -/
theorem thm_cn_iv_mean (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 2 ≤ T) (A S : ℕ) :
    ((A : ℝ) ^ 2 * ((1 / T : ℝ) ^ 2 * fanΛ₂ d z)
      + A * (1 / T * (w z m ^ 2 - (w z (x true) ^ 2 + w z (x false) ^ 2) / 2)
        - 4 * (1 / T : ℝ) ^ 2 * D * (D + w z m))) * S ^ 2 ≤
      meanLength (fanW d T) (S • (1, -1 - (A : ℤ))) ^ 2 := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have H := fanWs_lip hd (by omega : 0 < T)
  have hLf := fanL_bd hd
  have hX := fanL_sq_bd hd
  have hXm := thm_cn_iv_telescope hd hT
  set θ : ℝ := 1 / T with hθ
  have hθ0 : 0 < θ := by positivity
  show _ ≤ nm (df (fanWs d T) 0 (S • (1, -1 - (A : ℤ)))) ^ 2
  rw [nm_sq (H.bd _ _)]
  obtain ⟨hZb, hZm⟩ := mean_steps (F := fun n b i _ => fanL d z n b i ^ 2) hX S
  have hsh := hLf.shift S 0
  have h4 : mean ((fun n b i _ => fanL d z n b (i + S) : Fn) * (fun n b i _ => fanL d z n b (i + S) : Fn)) =
      fanΛ₂ d z := mean_shift_left (hLf.mul hLf) S
  have h3 : mean ((A * S * θ) ^ 2 • ((fun n b i _ => fanL d z n b (i + S) : Fn) *
        (fun n b i _ => fanL d z n b (i + S) : Fn))
      + ((A * S * θ) • (fun n b i k => (n : ℝ) ^ 2 * (fanL d z n b (i + S) ^ 2 - fanL d z n b i ^ 2) : Fn)
      + (fun _ _ _ _ => -(4 * A * θ ^ 2 * S ^ 2 * D * (D + w z m)) : Fn))) ≤
      mean (df (fanWs d T) 0 (S • (1, -1 - (A : ℤ))) * df (fanWs d T) 0 (S • (1, -1 - (A : ℤ)))) := by
    apply mean_mono (((hsh.mul hsh).smul _).add ((hZb.smul _).add (Bd.const _)))
      ((H.bd _ _).mul (H.bd _ _))
    filter_upwards [eventually_large hT (A * S)] with n hnn b i hi k hk
    have e0 : df (fanWs d T) 0 (S • (1, -1 - (A : ℤ))) n b i k =
        fanWs d T n b (i, k) (i + S, k - S - (A * S : ℕ)) := by
      simp only [df, add_zero, Prod.smul_mk, prod_add_mk]
      congr 2
      · simp
      · simp only [nsmul_eq_mul]
        push_cast
        ring
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [e0]
    linarith [thm_cn_iv_square hd hT A S hnn b hi hk]
  rw [mean_add ((hsh.mul hsh).smul _) ((hZb.smul _).add (Bd.const _)),
    mean_smul (hsh.mul hsh), mean_add (hZb.smul _) (Bd.const _), mean_smul hZb, mean_const,
    hZm, h4] at h3
  have h5 : (A * S * θ) * (S * (w z m ^ 2 - (w z (x true) ^ 2 + w z (x false) ^ 2) / 2)) ≤ (A * S * θ) *
      (S * mean (fun n b i k => (n : ℝ) ^ 2 * (fanL d z n b (i + 1) ^ 2 - fanL d z n b i ^ 2))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hXm (Nat.cast_nonneg S)
  refine le_trans ?_ h3
  nlinarith

/-- **Claim (iv)** of the proof of Theorem thm:cn: "N(1,−1−A)² ≥ A²θ²Λ₂ + AθΓ − O(Aθ²)", with
Γ = |mz|² − ½|xz|² − ½|vz|² and with 4D(D + |zm|) for the constant in O, which depends on neither A nor θ. ("Divide by S²";
"for lower bounds it is enough to prove them for ν(Sg)/S for every S".) -/
theorem thm_cn_iv (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 2 ≤ T) (A : ℕ) :
    (A : ℝ) ^ 2 * ((1 / T : ℝ) ^ 2 * fanΛ₂ d z)
      + A * (1 / T * (w z m ^ 2 - (w z (x true) ^ 2 + w z (x false) ^ 2) / 2) - 4 * (1 / T : ℝ) ^ 2 * D * (D + w z m)) ≤
      meanNorm (fanW d T) (1, -1 - (A : ℤ)) ^ 2 := by
  set Q := (A : ℝ) ^ 2 * ((1 / T : ℝ) ^ 2 * fanΛ₂ d z)
    + A * (1 / T * (w z m ^ 2 - (w z (x true) ^ 2 + w z (x false) ^ 2) / 2) - 4 * (1 / T : ℝ) ^ 2 * D * (D + w z m))
    with hQdef
  rcases lt_or_ge Q 0 with h | hQ
  · exact h.le.trans (sq_nonneg _)
  have h1 : √Q ≤ meanNorm (fanW d T) (1, -1 - (A : ℤ)) := by
    refine le_meanNorm _ _ fun S _ => (abs_le_of_sq_le_sq' ?_ (meanLength_nonneg _ _)).2
    rw [mul_pow, Real.sq_sqrt hQ]
    exact thm_cn_iv_mean hd hT A S
  calc Q = √Q ^ 2 := (Real.sq_sqrt hQ).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2

/-- **The end** of the proof of Theorem thm:cn. "By Lemma lem:means the second differences of l ↦ N(1,−1−l)² are 2N(0,1)², so
by (iii) ψ(l) = N(1,−1−l)² − l²θ²Λ₂ is concave on l = −1, 0, 1, …, so ψ(A) ≤ ψ(0) + A(ψ(0) − ψ(−1)). Insert (i), (ii), (iv),
divide by A and let A → ∞: θΓ − O(θ²) ≤ D²(−θ + θ²) + θ²Λ₂." -/
theorem thm_cn_end (hd : ∀ n, IsFan K w x m z D T (max n 1) (d n)) (hT : 2 ≤ T)
    (hxx : w (x true) (x false) = 2 * D) :
    1 / T * (w z m ^ 2 - (w z (x true) ^ 2 + w z (x false) ^ 2) / 2) - 4 * (1 / T : ℝ) ^ 2 * D * (D + w z m) ≤
      D ^ 2 * (-(1 / T) + (1 / T : ℝ) ^ 2) + (1 / T : ℝ) ^ 2 * fanΛ₂ d z := by
  have hT0 : 0 < T := by omega
  have par := lem_means_norm (fanW_price hd) (thm_cn_lipschitz hd hT0)
  have s1 := thm_cn_i hd hT hxx
  have s2 := thm_cn_ii hd hT
  have s3 := thm_cn_iii hd hT
  have s4 := thm_cn_iv hd hT
  set N := meanNorm (fanW d T) with hN
  set θ : ℝ := 1 / T with hθ
  set Λ₂ := fanΛ₂ d z with hΛ
  set Gc := w z m ^ 2 - (w z (x true) ^ 2 + w z (x false) ^ 2) / 2 with hG
  have c0 : N (1, -1 - ((1 : ℕ) : ℤ)) ^ 2 + N (1, 0) ^ 2 ≤
      2 * N (1, -1 - ((0 : ℕ) : ℤ)) ^ 2 + 2 * (θ ^ 2 * Λ₂) := by
    have h := par (1, -1) (0, 1)
    norm_num at h ⊢
    linarith
  have c1 : ∀ j : ℕ, N (1, -1 - ((j + 2 : ℕ) : ℤ)) ^ 2 + N (1, -1 - (j : ℤ)) ^ 2 ≤
      2 * N (1, -1 - ((j + 1 : ℕ) : ℤ)) ^ 2 + 2 * (θ ^ 2 * Λ₂) := by
    intro j
    have h := par (1, -1 - ((j + 1 : ℕ) : ℤ)) (0, 1)
    have e1 : ((1, -1 - ((j + 1 : ℕ) : ℤ)) : ℤ × ℤ) + (0, 1) = (1, -1 - (j : ℤ)) := by
      ext
      · simp
      · simp
        ring
    have e2 : ((1, -1 - ((j + 1 : ℕ) : ℤ)) : ℤ × ℤ) - (0, 1) = (1, -1 - ((j + 2 : ℕ) : ℤ)) := by
      ext
      · simp
      · simp
        ring
    rw [e1, e2] at h
    linarith
  have c2 := conc (f := fun j : ℕ => N (1, -1 - (j : ℤ)) ^ 2) (φ := N (1, 0) ^ 2) c0 c1
  simp only [Nat.cast_zero, sub_zero] at c2
  have hφ : D ^ 2 ≤ N (1, 0) ^ 2 := pow_le_pow_left₀ (fan_D_nonneg hd) s1 2
  set Δ := θ * Gc - 4 * θ ^ 2 * D * (D + w z m) - (N (1, -1) ^ 2 - N (1, 0) ^ 2 + θ ^ 2 * Λ₂) with hΔ
  have hA : ∀ A : ℕ, (A : ℝ) * Δ ≤ N (1, -1) ^ 2 := by
    intro A
    have h1 := s4 A
    have h2 := c2 A
    rw [hΔ]
    nlinarith
  have hΔ0 : Δ ≤ 0 := by
    by_contra h
    push Not at h
    obtain ⟨A, hA'⟩ := exists_nat_gt (N (1, -1) ^ 2 / Δ)
    rw [div_lt_iff₀ h] at hA'
    linarith [hA A]
  rw [hΔ] at hΔ0
  linarith

end Claims

/-- **Paper: Theorem thm:cn.** "Let x, v, m, z be points of a price with |xm|, |vm| ≤ D and |xv| = 2D. Then
|zm|² ≤ ½|zx|² + ½|zv|² − D²." -/
theorem thm_cn {Y : Type} {w : Y → Y → ℝ} (hw : IsPrice K w) (x v m z : Y) {D : ℝ} (h1 : w x m ≤ D) (h2 : w v m ≤ D)
    (h3 : w x v = 2 * D) : w z m ^ 2 ≤ 1 / 2 * w z x ^ 2 + 1 / 2 * w z v ^ 2 - D ^ 2 := by
  have hD0 : 0 ≤ D := (hw.nonneg _ _).trans h1
  have hB0 : 0 ≤ w z m := hw.nonneg _ _
  -- for θ = 1/T: divide by θ
  have key : ∀ T : ℕ, 2 ≤ T → w z m ^ 2 - (w z x ^ 2 + w z v ^ 2) / 2 + D ^ 2 ≤
      1 / T * (D ^ 2 + (D + w z m) ^ 2 + 4 * D * (D + w z m)) := by
    intro T hT
    have hT0 : 0 < T := by omega
    have hθ0 : (0 : ℝ) < 1 / T := by
      have : (0 : ℝ) < T := by exact_mod_cast hT0
      positivity
    choose d hd using fun n : ℕ => thm_cn_fan hw (fun b => cond b x v) m z
      (by intro b; cases b <;> assumption) hT0 (max_one_pos n)
    have h4 := thm_cn_end hd hT h3
    have h5 := mul_le_mul_of_nonneg_left (thm_cn_Λ₂_le hd) (sq_nonneg (1 / T : ℝ))
    simp only [cond_true, cond_false] at h4
    refine le_of_mul_le_mul_left ?_ hθ0
    nlinarith
  -- let θ → 0
  have hT : Tendsto (fun T : ℕ => 1 / (T : ℝ) * (D ^ 2 + (D + w z m) ^ 2 + 4 * D * (D + w z m)))
      atTop (𝓝 (0 * (D ^ 2 + (D + w z m) ^ 2 + 4 * D * (D + w z m)))) :=
    tendsto_one_div_atTop_nhds_zero_nat.mul_const _
  rw [zero_mul] at hT
  have h4 := ge_of_tendsto hT (by
    filter_upwards [eventually_ge_atTop 2] with T hT
    exact key T hT)
  linarith

end Paper
end


theorem solution {K : Type} [Field K] {Y : Type} {w : Y → Y → ℝ}
    (hw : Nc.Price.IsPrice K w) (x v m z : Y) {D : ℝ}
    (h1 : w x m ≤ D) (h2 : w v m ≤ D) (h3 : w x v = 2 * D) :
    w z m ^ 2 ≤ 1 / 2 * w z x ^ 2 + 1 / 2 * w z v ^ 2 - D ^ 2 :=
  Paper.thm_cn hw x v m z h1 h2 h3
