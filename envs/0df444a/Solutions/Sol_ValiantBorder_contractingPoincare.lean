-- Prove2me | solution 1 for ValiantBorder.contractingPoincare
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:13:49.142613+00:00
-- url     : https://prove2.me/submissions/47372a48-23f4-4f23-ad8d-e0c96b181059

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_cutLaws
import Theorems.Thm_ValiantBorder_priceMetricRealization

open Finset Nc.Tower
/-! Claude (Anthropic), *VP ≠ VNP over every field*, section on exchange identities.
Adapted from the public Lean release at revision 11b6c7e3c927df2658f513b6b68ea7f8929c62c5,
https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp .
The gate model for this project is in the mission's public statement file. -/
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Length functions on a group, matrices over F₂ and averages over pairs of invertible matrices
-/

open Finset Matrix

namespace Nc.Flag

/-- A length function: `dist z (g • z)` for an isometric action. -/
structure Len (G : Type*) [Group G] where
  /-- the value -/
  val : G → ℝ
  one' : val 1 = 0
  inv' : ∀ g, val g⁻¹ = val g
  mul' : ∀ g h, val (g * h) ≤ val g + val h

namespace Len
variable {G : Type*} [Group G] (l : Len G)

theorem nonneg (g : G) : 0 ≤ l.val g := by
  have h := l.mul' g g⁻¹
  rw [mul_inv_cancel, l.one', l.inv'] at h
  linarith

theorem conj (g h : G) : l.val (g * h * g⁻¹) ≤ 2 * l.val g + l.val h := by
  have h1 := l.mul' (g * h) g⁻¹
  have h2 := l.mul' g h
  rw [l.inv'] at h1
  linarith

end Len

/-- Minkowski for square sums. -/
theorem sqrt_sum_le {α : Type*} (s : Finset α) (a b c : α → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) (h : ∀ i, c i ≤ a i + b i) :
    √(∑ i ∈ s, c i ^ 2) ≤ √(∑ i ∈ s, a i ^ 2) + √(∑ i ∈ s, b i ^ 2) := by
  have hA : 0 ≤ ∑ i ∈ s, a i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i ∈ s, b i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  apply Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have hcs : ∑ i ∈ s, a i * b i ≤ √(∑ i ∈ s, a i ^ 2) * √(∑ i ∈ s, b i ^ 2) := by
    rw [← Real.sqrt_mul hA]
    apply Real.le_sqrt_of_sq_le
    exact sum_mul_sq_le_sq_mul_sq s a b
  calc ∑ i ∈ s, c i ^ 2 ≤ ∑ i ∈ s, (a i + b i) ^ 2 :=
        sum_le_sum fun i _ => pow_le_pow_left₀ (hc i) (h i) 2
    _ = ∑ i ∈ s, a i ^ 2 + 2 * ∑ i ∈ s, a i * b i + ∑ i ∈ s, b i ^ 2 := by
        rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
        exact sum_congr rfl fun i _ => by ring
    _ ≤ _ := by
        rw [add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
        linarith



variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Invertible matrices. -/
abbrev GLM (ι : Type*) [Fintype ι] [DecidableEq ι] := (Matrix ι ι F2)ˣ

noncomputable instance : Fintype (GLM ι) := Fintype.ofFinite _

/-- The sum of `f(PMQ)²` over invertible `P`, `Q`. -/
noncomputable def DM (f : Matrix ι ι F2 → ℝ) (M : Matrix ι ι F2) : ℝ :=
  ∑ p : GLM ι, ∑ q : GLM ι, f ((p : Matrix ι ι F2) * M * (q : Matrix ι ι F2)) ^ 2

theorem DM_mul (f : Matrix ι ι F2 → ℝ) (a b : GLM ι) (M : Matrix ι ι F2) :
    DM f ((a : Matrix ι ι F2) * M * (b : Matrix ι ι F2)) = DM f M := by
  unfold DM
  rw [← Equiv.sum_comp (Equiv.mulRight a)
    (fun p : GLM ι => ∑ q : GLM ι, f ((p : Matrix ι ι F2) * M * (q : Matrix ι ι F2)) ^ 2)]
  refine sum_congr rfl fun p _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft b)
    (fun q : GLM ι => f (((Equiv.mulRight a p : GLM ι) : Matrix ι ι F2) * M *
      (q : Matrix ι ι F2)) ^ 2)]
  refine sum_congr rfl fun q _ => ?_
  simp only [Equiv.coe_mulRight, Equiv.coe_mulLeft, Units.val_mul, Matrix.mul_assoc]

/-- The diagonal idempotent of a set of indices. -/
def dg (S : Finset ι) : Matrix ι ι F2 := Matrix.diagonal fun i => if i ∈ S then 1 else 0

theorem dg_empty : dg (∅ : Finset ι) = 0 := by
  simp [dg]

theorem dg_union {S T : Finset ι} (h : Disjoint S T) : dg (S ∪ T) = dg S + dg T := by
  unfold dg
  rw [Matrix.diagonal_add]
  congr 1
  funext i
  by_cases hS : i ∈ S
  · have hT : i ∉ T := Finset.disjoint_left.1 h hS
    simp [hS, hT]
  · simp [hS]

/-- The unit of a permutation. -/
def permU (σ : Equiv.Perm ι) : GLM ι where
  val := (1 : Matrix ι ι F2).submatrix σ id
  inv := (1 : Matrix ι ι F2).submatrix id σ
  val_inv := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply, σ.injective.eq_iff]
  inv_val := by
    rw [Matrix.submatrix_mul_equiv (1 : Matrix ι ι F2) (1 : Matrix ι ι F2) id σ id]
    simp

theorem permU_conj (σ : Equiv.Perm ι) (M : Matrix ι ι F2) :
    (permU σ : Matrix ι ι F2) * M * ((permU σ)⁻¹ : GLM ι) = M.submatrix σ σ := by
  ext i j
  simp [permU, Matrix.mul_apply, Matrix.one_apply]

theorem DM_dg_congr (f : Matrix ι ι F2 → ℝ) {S T : Finset ι} (h : S.card = T.card) :
    DM f (dg S) = DM f (dg T) := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm ι, ∀ i, σ i ∈ S ↔ i ∈ T := by
    have e : {i // i ∈ T} ≃ {i // i ∈ S} := Fintype.equivOfCardEq (by simp [h])
    refine ⟨e.extendSubtype, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
    · by_contra hT
      exact e.extendSubtype_not_mem i hT hi
    · exact e.extendSubtype_mem i hi
  rw [← DM_mul f (permU σ) ((permU σ)⁻¹) (dg S), permU_conj]
  congr 1
  ext i j
  simp only [dg, Matrix.submatrix_apply, Matrix.diagonal_apply, σ.injective.eq_iff, hσ]

theorem DM_dg_le (f : Matrix ι ι F2 → ℝ) (hf : ∀ M, 0 ≤ f M)
    (hadd : ∀ M N, f (M + N) ≤ f M + f N) {S T : Finset ι} (h : Disjoint S T) :
    √(DM f (dg (S ∪ T))) ≤ √(DM f (dg S)) + √(DM f (dg T)) := by
  unfold DM
  simp only [← Fintype.sum_prod_type']
  refine sqrt_sum_le univ _ _ _ (fun _ => hf _) (fun _ => hf _) (fun _ => hf _) fun x => ?_
  rw [dg_union h, Matrix.mul_add, Matrix.add_mul]
  exact hadd _ _

end Nc.Flag

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Section "Flat or contracting": quadrangles in a metric on the matrices over F₂

Definitions and lemmas for the proof of Theorem thm:alt (Paper/Alternative.lean). `nn w a W` is the paper's
n_a(W) = |a, a+W|², `BB w a W W'` is its B_a(W, W'), and `X p q S` is the matrix p·dg(S)·q: the matrices `X p q S` for
disjoint sets S, in one frame (p, q), are the transversal families (Nc/Flag/Transversal.lean).
-/

open Finset Matrix

namespace Nc.Flag

variable {m : ℕ}



variable {w : Mt m → Mt m → ℝ}

theorem madd_self (M : Mt m) : M + M = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero _

/-- The squared sides minus the squared diagonals of the quadrangle a, a+M, a+M+N, a+N. -/
def defect (w : Mt m → Mt m → ℝ) (a M N : Mt m) : ℝ :=
  w a (a + M) ^ 2 + w (a + M) (a + M + N) ^ 2 + w (a + M + N) (a + N) ^ 2 + w a (a + N) ^ 2 -
    (w a (a + M + N) ^ 2 + w (a + M) (a + N) ^ 2)

/-- The squared distance n_a(M) from `a` to `a + M`. -/
def nn (w : Mt m → Mt m → ℝ) (a M : Mt m) : ℝ := w a (a + M) ^ 2

theorem sum_defect (hw : ∀ a b, w a b = w b a) (M N : Mt m) :
    ∑ a, defect w a M N = 2 * (∑ a, nn w a M + ∑ a, nn w a N - ∑ a, nn w a (M + N)) := by
  have h1 : ∑ a, w (a + M) (a + M + N) ^ 2 = ∑ a, nn w a N :=
    Equiv.sum_comp (Equiv.addRight M) (fun a => nn w a N)
  have h2 : ∑ a, w (a + M + N) (a + N) ^ 2 = ∑ a, nn w a M := by
    rw [← Equiv.sum_comp (Equiv.addRight N) (fun a => nn w a M)]
    refine sum_congr rfl fun a _ => ?_
    show w (a + M + N) (a + N) ^ 2 = w (a + N) (a + N + M) ^ 2
    rw [hw, add_right_comm]
  have h3 : ∑ a, w (a + M) (a + N) ^ 2 = ∑ a, nn w a (M + N) := by
    rw [← Equiv.sum_comp (Equiv.addRight M) (fun a => nn w a (M + N))]
    refine sum_congr rfl fun a _ => ?_
    show w (a + M) (a + N) ^ 2 = w (a + M) (a + M + (M + N)) ^ 2
    have : a + M + (M + N) = a + N := by
      rw [add_assoc, ← add_assoc M M N, madd_self, zero_add]
    rw [this]
  have h4 : ∑ a, w a (a + M + N) ^ 2 = ∑ a, nn w a (M + N) := by
    refine sum_congr rfl fun a _ => ?_
    rw [nn, add_assoc]
  unfold defect
  simp only [sum_sub_distrib, sum_add_distrib]
  rw [h1, h2, h3, h4]
  show ∑ a, nn w a M + _ + _ + ∑ a, nn w a N - _ = _
  ring

/-- The matrix of a set of indices in a frame. -/
def X (p q : GLM (Fin m)) (S : Finset (Fin m)) : Mt m := (p : Mt m) * dg S * (q : Mt m)

theorem X_one (S : Finset (Fin m)) : X 1 1 S = dg S := by
  simp [X]

theorem X_empty (p q : GLM (Fin m)) : X p q ∅ = 0 := by
  simp [X, dg_empty]

theorem X_union (p q : GLM (Fin m)) {S T : Finset (Fin m)} (h : Disjoint S T) :
    X p q (S ∪ T) = X p q S + X p q T := by
  rw [X, dg_union h, Matrix.mul_add, Matrix.add_mul]
  rfl

/-- Every matrix is diagonal with entries 0 and 1 in some frame. -/
theorem exists_factor (M : Mt m) :
    ∃ (p q : GLM (Fin m)) (S : Finset (Fin m)), M = (p : Mt m) * dg S * (q : Mt m) := by
  obtain ⟨L, L', D, hM⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hu : ∀ L : List (TransvectionStruct (Fin m) F2),
      ∃ u : GLM (Fin m), (u : Mt m) = (L.map TransvectionStruct.toMatrix).prod := by
    intro L
    induction L with
    | nil => exact ⟨1, by simp⟩
    | cons t L ih =>
      obtain ⟨u, hu⟩ := ih
      refine ⟨⟨t.toMatrix, t.inv.toMatrix, t.mul_inv, t.inv_mul⟩ * u, ?_⟩
      rw [Units.val_mul, hu, List.map_cons, List.prod_cons]
  obtain ⟨u, hu1⟩ := hu L
  obtain ⟨v, hv1⟩ := hu L'
  refine ⟨u, v, univ.filter fun i => D i ≠ 0, ?_⟩
  have hD : Matrix.diagonal D = dg (univ.filter fun i => D i ≠ 0) := by
    unfold dg
    congr 1
    funext i
    have h2 : ∀ a : F2, a = if a ≠ 0 then 1 else 0 := by decide
    simpa using h2 (D i)
  rw [hM, hu1, hv1, hD]

theorem exists_X (M : Mt m) : ∃ (p q : GLM (Fin m)) (S : Finset (Fin m)), M = X p q S := exists_factor M

/-- The sum of |a, a + p·E·q|² over all a and all invertible p, q. -/
noncomputable def MD (w : Mt m → Mt m → ℝ) (E : Mt m) : ℝ := ∑ a, DM (fun M => w a (a + M)) E

theorem MD_eq (S : Finset (Fin m)) : MD w (dg S) =
    ∑ p : GLM (Fin m), ∑ q : GLM (Fin m), ∑ a, nn w a (X p q S) := by
  unfold MD DM
  rw [sum_comm]
  exact sum_congr rfl fun p _ => sum_comm

/-- The defects of the quadrangles with sides W = X p q S and W' = X p q T, added over all frames and all a. -/
theorem sum_all_defect (hw : ∀ a b, w a b = w b a) {S T : Finset (Fin m)} (h : Disjoint S T) :
    ∑ p : GLM (Fin m), ∑ q : GLM (Fin m), ∑ a, defect w a (X p q S) (X p q T) =
      2 * (MD w (dg S) + MD w (dg T) - MD w (dg (S ∪ T))) := by
  simp only [sum_defect hw, MD_eq]
  rw [← sum_add_distrib, ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [← sum_add_distrib, ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun q _ => ?_
  rw [X_union p q h]

/-- The scalar product B_a(M, N) = ½(n_a(M+N) − n_a(M) − n_a(N)). -/
noncomputable def BB (w : Mt m → Mt m → ℝ) (a M N : Mt m) : ℝ := (nn w a (M + N) - nn w a M - nn w a N) / 2

theorem BB_comm (a M N : Mt m) : BB w a M N = BB w a N M := by
  unfold BB
  rw [add_comm]
  ring

theorem add_cancel_left (M N : Mt m) : M + (M + N) = N := by
  rw [← add_assoc, madd_self, zero_add]

end Nc.Flag

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Section "Flat or contracting": transversal matrices

"We call W₁, W₂, … transversal if both their column spaces and their row spaces are independent." The theorem
`transversal_iff` says that this holds if and only if, for some invertible p and q, W_k = p·dg(S_k)·q with disjoint sets S_k.
-/

open Finset Matrix Submodule

namespace Nc.Flag

variable {m : ℕ}

/-- The column space of a matrix. -/
def colSpace (W : Mt m) : Submodule F2 (Fin m → F2) := span F2 (Set.range W.col)

/-- The row space of a matrix. -/
def rowSpace (W : Mt m) : Submodule F2 (Fin m → F2) := span F2 (Set.range W.row)

/-- "We call W₁, W₂, … transversal if both their column spaces and their row spaces are independent." -/
def Transversal {ι : Type} (W : ι → Mt m) : Prop :=
  iSupIndep (fun k => colSpace (W k)) ∧ iSupIndep fun k => rowSpace (W k)

theorem rowSpace_eq (W : Mt m) : rowSpace W = colSpace Wᵀ := by
  rw [rowSpace, colSpace, Matrix.col_transpose]

/-- The transpose of an invertible matrix. -/
def trU (p : GLM (Fin m)) : GLM (Fin m) where
  val := (p : Mt m)ᵀ
  inv := ((p⁻¹ : GLM (Fin m)) : Mt m)ᵀ
  val_inv := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem X_transpose (p q : GLM (Fin m)) (S : Finset (Fin m)) : (X p q S)ᵀ = X (trU q) (trU p) S := by
  rw [X, X, Matrix.transpose_mul, Matrix.transpose_mul, dg, Matrix.diagonal_transpose, Matrix.mul_assoc]
  rfl

theorem X_apply (p q : GLM (Fin m)) (S : Finset (Fin m)) (a b : Fin m) :
    X p q S a b = ∑ i ∈ S, (p : Mt m) a i * (q : Mt m) i b := by
  rw [X, Matrix.mul_apply, ← Finset.sum_filter_add_sum_filter_not univ (· ∈ S), Finset.filter_mem_eq_inter,
    Finset.univ_inter, Finset.sum_eq_zero (s := univ.filter fun i => i ∉ S), add_zero]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [dg, Matrix.mul_diagonal, if_pos hi, mul_one]
  · intro i hi
    rw [dg, Matrix.mul_diagonal, if_neg (Finset.mem_filter.1 hi).2, mul_zero, zero_mul]

theorem linearIndependent_col (p : GLM (Fin m)) : LinearIndependent F2 (p : Mt m).col :=
  Matrix.linearIndependent_cols_iff_isUnit.2 p.isUnit

/-- The column space of p·dg(S)·q is spanned by the columns of p in S. -/
theorem colSpace_X (p q : GLM (Fin m)) (S : Finset (Fin m)) :
    colSpace (X p q S) = span F2 ((p : Mt m).col '' S) := by
  refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
  · rintro _ ⟨b, rfl⟩
    have h : (X p q S).col b = ∑ i ∈ S, (q : Mt m) i b • (p : Mt m).col i := by
      ext a
      simp [Matrix.col, X_apply, mul_comm]
    rw [h]
    exact sum_mem fun i hi => smul_mem _ _ (subset_span (Set.mem_image_of_mem _ hi))
  · rintro _ ⟨i, hi, rfl⟩
    have h : (p : Mt m).col i = ∑ b, ((q⁻¹ : GLM (Fin m)) : Mt m) b i • (X p q S).col b := by
      ext a
      have h1 : (X p q S * ((q⁻¹ : GLM (Fin m)) : Mt m)) a i = (p : Mt m) a i := by
        rw [X, Units.mul_inv_cancel_right, dg, Matrix.mul_diagonal, if_pos (Finset.mem_coe.1 hi), mul_one]
      rw [Matrix.mul_apply] at h1
      simp only [Matrix.col, Matrix.transpose_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← h1]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    rw [SetLike.mem_coe, h]
    exact sum_mem fun b _ => smul_mem _ _ (subset_span (Set.mem_range_self b))

theorem iSupIndep_colSpace {ι : Type} (p q : GLM (Fin m)) (S : ι → Finset (Fin m))
    (hd : ∀ k l, k ≠ l → Disjoint (S k) (S l)) : iSupIndep fun k => colSpace (X p q (S k)) := by
  intro k
  simp only [colSpace_X]
  have h1 : ⨆ (j) (_ : j ≠ k), span F2 ((p : Mt m).col '' (S j : Set (Fin m))) ≤
      span F2 ((p : Mt m).col '' ⋃ (j) (_ : j ≠ k), (S j : Set (Fin m))) :=
    iSup₂_le fun j hj => span_mono (Set.image_mono (Set.subset_iUnion₂ (s := fun j (_ : j ≠ k) => (S j : Set (Fin m))) j hj))
  refine Disjoint.mono_right h1 ((linearIndependent_col p).disjoint_span_image ?_)
  rw [Set.disjoint_iUnion₂_right]
  exact fun j hj => Finset.disjoint_coe.2 (hd k j hj.symm)

theorem exists_perm_comp {α : Type} (f g : α → Fin m) (hf : f.Injective) (hg : g.Injective) :
    ∃ σ : Equiv.Perm (Fin m), ∀ k, σ (f k) = g k := by
  classical
  let e : {x // x ∈ Set.range f} ≃ {x // x ∈ Set.range g} :=
    (Equiv.ofInjective f hf).symm.trans (Equiv.ofInjective g hg)
  refine ⟨e.extendSubtype, fun k => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (f k) (Set.mem_range_self k)]
  have : (Equiv.ofInjective f hf).symm ⟨f k, Set.mem_range_self k⟩ = k :=
    Equiv.ofInjective_symm_apply hf k
  simp [e, this]

/-- Linearly independent vectors are columns, at given places, of an invertible matrix. -/
theorem exists_glm_col {α : Type} (v : α → Fin m → F2) (hv : LinearIndependent F2 v) (ε : α → Fin m)
    (hε : ε.Injective) : ∃ P : GLM (Fin m), ∀ k, (P : Mt m).col (ε k) = v k := by
  classical
  have hs := hv.linearIndepOn_id
  let b := Module.Basis.extend hs
  have : Fintype (hs.extend (Set.subset_univ _)) := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card (hs.extend (Set.subset_univ _)) = m := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fin_fun]
  let e₀ : hs.extend (Set.subset_univ _) ≃ Fin m := Fintype.equivFinOfCardEq hcard
  let u : α → hs.extend (Set.subset_univ _) := fun k => ⟨v k, hs.subset_extend _ (Set.mem_range_self k)⟩
  have hu : (fun k => e₀ (u k)).Injective := fun k l h =>
    hv.injective (congrArg Subtype.val (e₀.injective h))
  obtain ⟨σ, hσ⟩ := exists_perm_comp (fun k => e₀ (u k)) ε hu hε
  let c : Module.Basis (Fin m) F2 (Fin m → F2) := b.reindex (e₀.trans σ)
  have hc : ∀ k, c (ε k) = v k := by
    intro k
    have h1 : (e₀.trans σ).symm (ε k) = u k := by
      rw [Equiv.symm_apply_eq]
      exact (hσ k).symm
    rw [Module.Basis.reindex_apply, h1]
    exact Module.Basis.extend_apply_self hs _
  have hA : IsUnit (Matrix.of fun i j => c j i : Mt m) :=
    Matrix.linearIndependent_cols_iff_isUnit.1 c.linearIndependent
  exact ⟨hA.unit, fun k => hc k⟩

/-- Linearly independent vectors are rows, at given places, of an invertible matrix. -/
theorem exists_glm_row {α : Type} (v : α → Fin m → F2) (hv : LinearIndependent F2 v) (ε : α → Fin m)
    (hε : ε.Injective) : ∃ Q : GLM (Fin m), ∀ k, (Q : Mt m).row (ε k) = v k := by
  obtain ⟨P, hP⟩ := exists_glm_col v hv ε hε
  exact ⟨trU P, hP⟩

theorem linearIndependent_sigma {ι : Type} {W : ι → Mt m} (h : iSupIndep fun k => colSpace (W k))
    (p q : ι → GLM (Fin m)) (S : ι → Finset (Fin m)) (hW : ∀ k, W k = X (p k) (q k) (S k)) :
    LinearIndependent F2 fun x : Σ k, S k => (p x.1 : Mt m).col x.2 := by
  have hle : ∀ k, span F2 (Set.range fun i : S k => (p k : Mt m).col i) ≤ colSpace (W k) := by
    intro k
    rw [hW k, colSpace_X]
    refine span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Set.mem_image_of_mem _ i.2
  refine linearIndependent_iUnion_finite (f := fun k (i : S k) => (p k : Mt m).col i)
    (fun k => (linearIndependent_col (p k)).comp _ Subtype.val_injective) fun k t _ hk => ?_
  refine (h k).mono (hle k) (iSup₂_le fun j hj => ?_)
  exact le_iSup₂_of_le (f := fun j (_ : j ≠ k) => colSpace (W j)) j (fun e => hk (e ▸ hj)) (hle j)

/-- Matrices are transversal if and only if in some frame (p, q) they are diagonal, with entries 0 and 1 and with
disjoint supports. -/
theorem transversal_iff {ι : Type} [Fintype ι] (W : ι → Mt m) :
    Transversal W ↔ ∃ (p q : GLM (Fin m)) (S : ι → Finset (Fin m)),
      (∀ k l, k ≠ l → Disjoint (S k) (S l)) ∧ ∀ k, W k = X p q (S k) := by
  classical
  constructor
  · rintro ⟨hc, hr⟩
    choose p q S hW using fun k => exists_X (W k)
    have hv := linearIndependent_sigma hc p q S hW
    have hv' : LinearIndependent F2 fun x : Σ k, S k => (q x.1 : Mt m).row x.2 := by
      simp only [rowSpace_eq] at hr
      exact linearIndependent_sigma hr (fun k => trU (q k)) (fun k => trU (p k)) S
        fun k => by rw [hW k, X_transpose]
    have hcard : Fintype.card (Σ k, S k) ≤ Fintype.card (Fin m) := by
      have := hv.fintype_card_le_finrank
      rw [Module.finrank_fin_fun] at this
      exact this.trans (Fintype.card_fin m).ge
    obtain ⟨ε⟩ := Function.Embedding.nonempty_of_card_le hcard
    obtain ⟨P, hP⟩ := exists_glm_col _ hv ε ε.injective
    obtain ⟨Q, hQ⟩ := exists_glm_row _ hv' ε ε.injective
    refine ⟨P, Q, fun k => univ.image fun i : S k => ε ⟨k, i⟩, fun k l hkl => ?_, fun k => ?_⟩
    · rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hx'
      exact hkl (congrArg Sigma.fst (ε.injective hj)).symm
    · ext a b
      rw [hW k, X_apply, X_apply, Finset.sum_image fun i _ j _ h => by
        simpa using ε.injective h, ← Finset.sum_coe_sort (S k)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 := congrFun (hP ⟨k, i⟩) a
      have h2 := congrFun (hQ ⟨k, i⟩) b
      simp only [Matrix.col, Matrix.row, Matrix.transpose_apply] at h1 h2
      rw [h1, h2]
  · rintro ⟨p, q, S, hd, hW⟩
    have e : W = fun k => X p q (S k) := funext hW
    subst e
    refine ⟨iSupIndep_colSpace p q S hd, ?_⟩
    simp only [rowSpace_eq, X_transpose]
    exact iSupIndep_colSpace _ _ S hd

end Nc.Flag

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Section "Flat or contracting", step "Rank one": vectors and matrices of rank one

Linear algebra over F₂ for the proof of Theorem thm:alt (Paper/Alternative.lean). The matrix u xᵀ is `vecMulVec u x`. For
nonzero u₁x₁ᵀ and u₂x₂ᵀ, the matrices W, u₁x₁ᵀ, u₂x₂ᵀ are transversal if and only if u₁, u₂ are independent modulo the column space of W, and x₁, x₂ modulo
its row space (`transversal_vec_iff`). The lemma `connect` joins any two vectors outside a subspace of codimension at least 2 by
steps x ↦ x + y with x, y independent modulo the subspace.
-/

open Finset Matrix Submodule

namespace Nc.Flag

variable {m : ℕ} {A : Submodule F2 (Fin m → F2)}

theorem vadd_self (u : Fin m → F2) : u + u = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero _

theorem vadd_cancel_left (u v : Fin m → F2) : u + (u + v) = v := by
  rw [← add_assoc, vadd_self, zero_add]

theorem mem_span_singleton_F2 {u v : Fin m → F2} : v ∈ span F2 {u} ↔ v = 0 ∨ v = u := by
  rw [mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    have h : a = 0 ∨ a = 1 := by
      revert a
      decide
    rcases h with rfl | rfl
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr (one_smul _ _)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

theorem mem_sup_span_F2 {u v : Fin m → F2} : v ∈ A ⊔ span F2 {u} ↔ v ∈ A ∨ v + u ∈ A := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    rcases mem_span_singleton_F2.1 hz with rfl | rfl
    · exact Or.inl (by rwa [add_zero])
    · exact Or.inr (by rwa [add_assoc, vadd_self, add_zero])
  · rintro (h | h)
    · exact ⟨v, h, 0, zero_mem _, add_zero _⟩
    · exact ⟨v + u, h, u, mem_span_singleton_self u, by rw [add_assoc, vadd_self, add_zero]⟩

/-- The vectors u₁, u₂ are independent modulo the subspace A: none of u₁, u₂, u₁ + u₂ lies in A. In other words, u₁ is
outside A, and u₂ is outside the span of u₁ with A. -/
def Indep2 (A : Submodule F2 (Fin m → F2)) (u₁ u₂ : Fin m → F2) : Prop := u₁ ∉ A ∧ u₂ ∉ A ∧ u₁ + u₂ ∉ A

theorem indep2_iff {u₁ u₂ : Fin m → F2} : Indep2 A u₁ u₂ ↔ u₁ ∉ A ∧ u₂ ∉ A ⊔ span F2 {u₁} := by
  rw [mem_sup_span_F2, not_or, add_comm u₂ u₁]
  rfl

theorem Indep2.symm {u₁ u₂ : Fin m → F2} (h : Indep2 A u₁ u₂) : Indep2 A u₂ u₁ :=
  ⟨h.2.1, h.1, by rw [add_comm]; exact h.2.2⟩

theorem Indep2.add_right {u₁ u₂ : Fin m → F2} (h : Indep2 A u₁ u₂) : Indep2 A u₁ (u₁ + u₂) :=
  ⟨h.1, h.2.2, by rw [vadd_cancel_left]; exact h.2.1⟩

theorem Indep2.add_left {u₁ u₂ : Fin m → F2} (h : Indep2 A u₁ u₂) : Indep2 A (u₁ + u₂) u₂ :=
  ⟨h.2.2, h.2.1, by rw [add_assoc, vadd_self, add_zero]; exact h.1⟩

theorem exists_notMem (hA : Module.finrank F2 A < m) : ∃ u, u ∉ A := by
  by_contra h
  push Not at h
  have : A = ⊤ := eq_top_iff.2 fun u _ => h u
  rw [this, finrank_top, Module.finrank_fin_fun] at hA
  exact lt_irrefl _ hA

/-- Outside a subspace of codimension at least 2, every vector has a second one that is independent of it. -/
theorem exists_indep2 (hA : Module.finrank F2 A + 2 ≤ m) {u : Fin m → F2} (hu : u ∉ A) : ∃ v, Indep2 A u v := by
  have h1 : Module.finrank F2 (A ⊔ span F2 {u} : Submodule F2 (Fin m → F2)) < m := by
    have h2 := Submodule.finrank_add_le_finrank_add_finrank A (span F2 {u})
    have h3 : Module.finrank F2 (span F2 {u}) ≤ 1 := by
      have := finrank_span_le_card (R := F2) ({u} : Set (Fin m → F2))
      simpa using this
    omega
  obtain ⟨v, hv⟩ := exists_notMem h1
  exact ⟨v, indep2_iff.2 ⟨hu, hv⟩⟩

/-- "Such moves connect all vectors outside" a subspace R of codimension at least 2: a function that does not change when x
becomes x + y, for x, y independent modulo R, has one value outside R. -/
theorem connect {R : Submodule F2 (Fin m → F2)} (hR : Module.finrank F2 R + 2 ≤ m) {g : (Fin m → F2) → ℝ}
    (hg : ∀ x y, Indep2 R x y → g (x + y) = g x) {x x' : Fin m → F2} (hx : x ∉ R) (hx' : x' ∉ R) : g x = g x' := by
  by_cases h : x + x' ∈ R
  · obtain ⟨z, hz⟩ := exists_indep2 hR hx
    have h1 : z + (x + x') ∉ R := fun h2 => hz.2.1 (by simpa using R.sub_mem h2 h)
    have e : x + z + (z + (x + x')) = x' := by
      rw [add_assoc, vadd_cancel_left, vadd_cancel_left]
    have h2 := hg (x + z) (z + (x + x')) ⟨hz.2.2, h1, by rwa [e]⟩
    rw [e] at h2
    rw [h2, hg x z hz]
  · have h2 := hg x (x + x') ⟨hx, h, by rwa [vadd_cancel_left]⟩
    rw [vadd_cancel_left] at h2
    exact h2.symm

/-! ### Matrices u xᵀ -/

theorem vec_ne_zero {u x : Fin m → F2} : vecMulVec u x ≠ 0 ↔ u ≠ 0 ∧ x ≠ 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩ <;> rintro rfl <;> simp at h
  · rintro ⟨hu, hx⟩ h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
    have := congrFun (congrFun h i) j
    rw [vecMulVec_apply] at this
    exact (mul_ne_zero hi hj) this

theorem colSpace_vec (u : Fin m → F2) {x : Fin m → F2} (hx : x ≠ 0) : colSpace (vecMulVec u x) = span F2 {u} := by
  have hc : ∀ j, (vecMulVec u x).col j = x j • u := fun j => by
    funext i
    simp [Matrix.col, vecMulVec_apply, mul_comm]
  refine le_antisymm (span_le.2 ?_) (span_le.2 ?_)
  · rintro _ ⟨j, rfl⟩
    rw [hc]
    exact smul_mem _ _ (mem_span_singleton_self u)
  · rintro _ rfl
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
    have h1 : x j = 1 := by
      have : ∀ a : F2, a ≠ 0 → a = 1 := by decide
      exact this _ hj
    refine subset_span ⟨j, ?_⟩
    rw [hc, h1, one_smul]

theorem rowSpace_vec {u : Fin m → F2} (hu : u ≠ 0) (x : Fin m → F2) : rowSpace (vecMulVec u x) = span F2 {x} := by
  rw [rowSpace_eq, transpose_vecMulVec, colSpace_vec x hu]

theorem colSpace_zero : colSpace (0 : Mt m) = ⊥ := by
  refine (span_eq_bot).2 ?_
  rintro _ ⟨j, rfl⟩
  rfl

theorem rowSpace_zero : rowSpace (0 : Mt m) = ⊥ := by
  rw [rowSpace_eq, transpose_zero, colSpace_zero]

theorem finrank_colSpace (W : Mt m) : Module.finrank F2 (colSpace W) = W.rank :=
  (Matrix.rank_eq_finrank_span_cols W).symm

theorem finrank_rowSpace (W : Mt m) : Module.finrank F2 (rowSpace W) = W.rank :=
  (Matrix.rank_eq_finrank_span_row W).symm

theorem rank_vec {u x : Fin m → F2} (hu : u ≠ 0) (hx : x ≠ 0) : (vecMulVec u x).rank = 1 := by
  rw [← finrank_colSpace, colSpace_vec u hx, finrank_span_singleton hu]

/-! ### Independent subspaces -/

theorem iSupIndep_two {B C : Submodule F2 (Fin m → F2)} : iSupIndep ![B, C] ↔ Disjoint B C :=
  iSupIndep_pair (i := 0) (j := 1) (by decide) (by decide)

theorem iSupIndep_three {B C D : Submodule F2 (Fin m → F2)} :
    iSupIndep ![B, C, D] ↔ Disjoint B (C ⊔ D) ∧ Disjoint C (B ⊔ D) ∧ Disjoint D (B ⊔ C) := by
  have e0 : (⨆ (j : Fin 3) (_ : j ≠ 0), ![B, C, D] j) = C ⊔ D := by
    refine le_antisymm (iSup₂_le fun j hj => ?_) (sup_le (le_iSup₂_of_le 1 (by decide) le_rfl)
      (le_iSup₂_of_le 2 (by decide) le_rfl))
    fin_cases j
    · exact absurd rfl hj
    · exact le_sup_left
    · exact le_sup_right
  have e1 : (⨆ (j : Fin 3) (_ : j ≠ 1), ![B, C, D] j) = B ⊔ D := by
    refine le_antisymm (iSup₂_le fun j hj => ?_) (sup_le (le_iSup₂_of_le 0 (by decide) le_rfl)
      (le_iSup₂_of_le 2 (by decide) le_rfl))
    fin_cases j
    · exact le_sup_left
    · exact absurd rfl hj
    · exact le_sup_right
  have e2 : (⨆ (j : Fin 3) (_ : j ≠ 2), ![B, C, D] j) = B ⊔ C := by
    refine le_antisymm (iSup₂_le fun j hj => ?_) (sup_le (le_iSup₂_of_le 0 (by decide) le_rfl)
      (le_iSup₂_of_le 1 (by decide) le_rfl))
    fin_cases j
    · exact le_sup_left
    · exact le_sup_right
    · exact absurd rfl hj
  rw [iSupIndep_def, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ]
  constructor
  · rintro ⟨h0, h1, h2, -⟩
    exact ⟨e0 ▸ h0, e1 ▸ h1, e2 ▸ h2⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨e0.symm ▸ h0, e1.symm ▸ h1, e2.symm ▸ h2, fun i => i.elim0⟩

theorem disjoint_span_F2 {u : Fin m → F2} (hu : u ≠ 0) : Disjoint A (span F2 {u}) ↔ u ∉ A := by
  rw [disjoint_def]
  constructor
  · intro h hA
    exact hu (h u hA (mem_span_singleton_self u))
  · intro h v hv hv'
    rcases mem_span_singleton_F2.1 hv' with rfl | rfl
    · rfl
    · exact absurd hv h

theorem iSupIndep_of_indep2 {u₁ u₂ : Fin m → F2} (h : Indep2 A u₁ u₂) :
    iSupIndep ![A, span F2 {u₁}, span F2 {u₂}] := by
  rw [iSupIndep_three]
  refine ⟨disjoint_def.2 fun v hv hv' => ?_, disjoint_def.2 fun v hv hv' => ?_, disjoint_def.2 fun v hv hv' => ?_⟩
  · rcases mem_sup_span_F2.1 hv' with h1 | h1 <;> rcases mem_span_singleton_F2.1 h1 with h2 | h2
    · exact h2
    · exact absurd (h2 ▸ hv) h.1
    · have : v = u₂ := by rw [← vadd_cancel_left u₂ v, add_comm u₂ v, h2, add_zero]
      exact absurd (this ▸ hv) h.2.1
    · have : v = u₁ + u₂ := by rw [← h2, add_assoc, vadd_self, add_zero]
      exact absurd (this ▸ hv) h.2.2
  · rcases mem_span_singleton_F2.1 hv with rfl | rfl
    · rfl
    · rcases mem_sup_span_F2.1 hv' with h1 | h1
      · exact absurd h1 h.1
      · exact absurd h1 h.2.2
  · rcases mem_span_singleton_F2.1 hv with rfl | rfl
    · rfl
    · rcases mem_sup_span_F2.1 hv' with h1 | h1
      · exact absurd h1 h.2.1
      · exact absurd (by rwa [add_comm] at h1) h.2.2

theorem indep2_of_iSupIndep {u₁ u₂ : Fin m → F2} (h1 : u₁ ≠ 0) (h2 : u₂ ≠ 0)
    (h : iSupIndep ![A, span F2 {u₁}, span F2 {u₂}]) : Indep2 A u₁ u₂ := by
  obtain ⟨d0, d1, -⟩ := iSupIndep_three.1 h
  rw [disjoint_def] at d0 d1
  have m1 : u₁ ∈ span F2 {u₁} := mem_span_singleton_self u₁
  have m2 : u₂ ∈ span F2 {u₂} := mem_span_singleton_self u₂
  refine ⟨fun hA => h1 (d0 _ hA (mem_sup_left m1)), fun hA => h2 (d0 _ hA (mem_sup_right m2)), fun hA => ?_⟩
  have e := d0 _ hA (add_mem (mem_sup_left m1) (mem_sup_right m2))
  have e' : u₁ = u₂ := by rw [← vadd_cancel_left u₁ u₂, e, add_zero]
  exact h1 (d1 _ m1 (mem_sup_right (e' ▸ m2)))

/-! ### Transversal matrices of rank one -/

theorem transversal_two {W V : Mt m} :
    Transversal ![W, V] ↔ Disjoint (colSpace W) (colSpace V) ∧ Disjoint (rowSpace W) (rowSpace V) := by
  have e1 : (fun k => colSpace (![W, V] k)) = ![colSpace W, colSpace V] := by
    funext k
    fin_cases k <;> rfl
  have e2 : (fun k => rowSpace (![W, V] k)) = ![rowSpace W, rowSpace V] := by
    funext k
    fin_cases k <;> rfl
  rw [Transversal, e1, e2, iSupIndep_two, iSupIndep_two]

theorem transversal_three {W V V' : Mt m} : Transversal ![W, V, V'] ↔
    iSupIndep ![colSpace W, colSpace V, colSpace V'] ∧ iSupIndep ![rowSpace W, rowSpace V, rowSpace V'] := by
  have e1 : (fun k => colSpace (![W, V, V'] k)) = ![colSpace W, colSpace V, colSpace V'] := by
    funext k
    fin_cases k <;> rfl
  have e2 : (fun k => rowSpace (![W, V, V'] k)) = ![rowSpace W, rowSpace V, rowSpace V'] := by
    funext k
    fin_cases k <;> rfl
  rw [Transversal, e1, e2]

/-- W and u xᵀ ≠ 0 are transversal if and only if u is outside the column space and x outside the row space of W. -/
theorem transversal_vec {W : Mt m} {u x : Fin m → F2} (hu : u ≠ 0) (hx : x ≠ 0) :
    Transversal ![W, vecMulVec u x] ↔ u ∉ colSpace W ∧ x ∉ rowSpace W := by
  rw [transversal_two, colSpace_vec u hx, rowSpace_vec hu x, disjoint_span_F2 hu, disjoint_span_F2 hx]

/-- W, u₁x₁ᵀ ≠ 0 and u₂x₂ᵀ ≠ 0 are transversal if and only if u₁, u₂ are independent modulo the column space of W and x₁, x₂
modulo its row space. -/
theorem transversal_vec_iff {W : Mt m} {u₁ u₂ x₁ x₂ : Fin m → F2} (h1 : vecMulVec u₁ x₁ ≠ 0)
    (h2 : vecMulVec u₂ x₂ ≠ 0) : Transversal ![W, vecMulVec u₁ x₁, vecMulVec u₂ x₂] ↔
      Indep2 (colSpace W) u₁ u₂ ∧ Indep2 (rowSpace W) x₁ x₂ := by
  obtain ⟨hu₁, hx₁⟩ := vec_ne_zero.1 h1
  obtain ⟨hu₂, hx₂⟩ := vec_ne_zero.1 h2
  rw [transversal_three, colSpace_vec u₁ hx₁, colSpace_vec u₂ hx₂, rowSpace_vec hu₁ x₁, rowSpace_vec hu₂ x₂]
  exact ⟨fun h => ⟨indep2_of_iSupIndep hu₁ hu₂ h.1, indep2_of_iSupIndep hx₁ hx₂ h.2⟩,
    fun h => ⟨iSupIndep_of_indep2 h.1, iSupIndep_of_indep2 h.2⟩⟩

theorem Indep2.ne_zero {u₁ u₂ : Fin m → F2} (h : Indep2 A u₁ u₂) : u₁ ≠ 0 ∧ u₂ ≠ 0 :=
  ⟨fun e => h.1 (e ▸ A.zero_mem), fun e => h.2.1 (e ▸ A.zero_mem)⟩

theorem transversal_of_indep2 {W : Mt m} {u₁ u₂ x₁ x₂ : Fin m → F2} (hu : Indep2 (colSpace W) u₁ u₂)
    (hx : Indep2 (rowSpace W) x₁ x₂) : Transversal ![W, vecMulVec u₁ x₁, vecMulVec u₂ x₂] :=
  (transversal_vec_iff (vec_ne_zero.2 ⟨hu.ne_zero.1, hx.ne_zero.1⟩) (vec_ne_zero.2 ⟨hu.ne_zero.2, hx.ne_zero.2⟩)).2
    ⟨hu, hx⟩

/-- The zero matrix is transversal to every matrix. -/
theorem transversal_zero (V : Mt m) : Transversal ![0, V] := by
  rw [transversal_two, colSpace_zero, rowSpace_zero]
  exact ⟨disjoint_bot_left, disjoint_bot_left⟩

/-- The last two of three transversal matrices are transversal. -/
theorem Transversal.tail {W V V' : Mt m} (h : Transversal ![W, V, V']) : Transversal ![V, V'] := by
  obtain ⟨h1, h2⟩ := transversal_three.1 h
  rw [iSupIndep_three] at h1 h2
  exact transversal_two.2 ⟨h1.2.1.mono_right le_sup_right, h2.2.1.mono_right le_sup_right⟩

/-- The matrix p·dg{i}·q is u xᵀ for the column u of p and the row x of q with the index i. -/
theorem X_singleton (p q : GLM (Fin m)) (i : Fin m) : X p q {i} = vecMulVec ((p : Mt m).col i) ((q : Mt m).row i) := by
  ext a b
  rw [X_apply, sum_singleton, vecMulVec_apply]
  rfl

theorem col_ne_zero (p : GLM (Fin m)) (i : Fin m) : (p : Mt m).col i ≠ 0 := (linearIndependent_col p).ne_zero i

theorem row_ne_zero (q : GLM (Fin m)) (i : Fin m) : (q : Mt m).row i ≠ 0 :=
  (Matrix.linearIndependent_rows_iff_isUnit.2 q.isUnit).ne_zero i

end Nc.Flag

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
# The metric of a finite ℓ²-product
-/

namespace Cat

variable {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MetricSpace (X i)]

theorem piLp_dist_sq (f g : PiLp 2 X) : dist f g ^ 2 = ∑ i, dist (f i) (g i) ^ 2 := by
  rw [PiLp.dist_eq_sum (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

end Cat

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "Prices are nonpositively curved": CAT(0) spaces

The definition of CAT(0) spaces and Lemma lem:toolkit, part by part. All of it rests on the inequality (CN) alone, which is
the class Cat.CN. Two predicates of the library are used in the proofs: Cat.IsPt x v t b says that b satisfies the inequality
of part (a), and Cat.IsBary w x b that b satisfies the inequality of part (c), for weights w.
-/

namespace Paper

open Finset Filter Topology Cat

/-- The paper's definition: "A complete metric space is CAT(0) if any two points x, v have a midpoint and (CN) holds
for it." -/
theorem cat0_iff (X : Type) [MetricSpace X] : Cat.CN X ↔ CompleteSpace X ∧ ∀ x v : X, ∃ m,
    dist x m = dist x v / 2 ∧ dist m v = dist x v / 2 ∧
      ∀ z, dist z m ^ 2 ≤ 1 / 2 * dist z x ^ 2 + 1 / 2 * dist z v ^ 2 - (dist x v / 2) ^ 2 := by
  constructor
  · intro h
    refine ⟨h.toCompleteSpace, fun x v => ⟨Cat.mid x v, Cat.dist_mid_left x v, Cat.dist_mid_right x v, fun z => ?_⟩⟩
    linarith [Cat.cn x v z]
  · rintro ⟨hc, h⟩
    refine { hc with exists_mid := fun x v => ?_ }
    obtain ⟨m, -, -, hm⟩ := h x v
    exact ⟨m, fun z => by linarith [hm z]⟩

section Toolkit

variable {Y : Type*} [MetricSpace Y] [CN Y]

/-- The minimization behind parts (a), (c) and (d): "Strict convexity of the functions to be minimized, from (CN), makes
minimizing sequences converge; comparing the minimum with points close to it on [b,y], respectively [Py,q], gives the
inequalities." Let C be nonempty, closed and convex, and let Θ ≥ 0 be continuous with
Θ(m) ≤ ½Θ(x) + ½Θ(v) − (c/4)|xv|² for the midpoint m of x, v ∈ C, where c > 0. Then some b ∈ C has Θ(y) ≥ Θ(b) + c|yb|² for all
y ∈ C. -/
theorem lem_toolkit_minimization (C : Set Y) (hC : IsClosed C) (hne : C.Nonempty)
    (hmem : ∀ x ∈ C, ∀ v ∈ C, mid x v ∈ C) (Θ : Y → ℝ) (hF : Continuous Θ)
    (hF0 : ∀ x, 0 ≤ Θ x) {c : ℝ} (hc : 0 < c)
    (hconv : ∀ x ∈ C, ∀ v ∈ C, Θ (mid x v) ≤ (Θ x + Θ v) / 2 - c / 4 * dist x v ^ 2) :
    ∃ b ∈ C, ∀ y ∈ C, Θ b + c * dist y b ^ 2 ≤ Θ y := by
  set I := sInf (Θ '' C) with hI
  have hbdd : BddBelow (Θ '' C) := ⟨0, by rintro _ ⟨x, -, rfl⟩; exact hF0 x⟩
  have hle : ∀ y ∈ C, I ≤ Θ y := fun y hy => csInf_le hbdd ⟨y, hy, rfl⟩
  have hseq : ∀ n : ℕ, ∃ y ∈ C, Θ y < I + 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := Real.lt_sInf_add_pos (hne.image Θ)
      (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
    exact ⟨y, hy, h⟩
  choose u huC hu using hseq
  have hcauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show 0 < c / 4 * ε ^ 2 by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hconv _ (huC m) _ (huC n)
    have h2 := hle _ (hmem _ (huC m) _ (huC n))
    have hmono : ∀ k : ℕ, N ≤ k → 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      intro k hk
      apply one_div_le_one_div_of_le (by positivity)
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have h3 := hu m
    have h4 := hu n
    have h5 := hmono m hm
    have h6 := hmono n hn
    have h7 : c / 4 * dist (u m) (u n) ^ 2 < c / 4 * ε ^ 2 := by linarith
    have h8 : dist (u m) (u n) ^ 2 < ε ^ 2 := lt_of_mul_lt_mul_left h7 (by positivity)
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h8
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hbC : b ∈ C := hC.mem_of_tendsto hb (Eventually.of_forall huC)
  have hFb : Θ b ≤ I := by
    have h1 : Tendsto (fun n => Θ (u n)) atTop (𝓝 (Θ b)) := (hF.tendsto b).comp hb
    have h2 : Tendsto (fun n : ℕ => I + 1 / ((n : ℝ) + 1)) atTop (𝓝 (I + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h2
    exact le_of_tendsto_of_tendsto' h1 h2 fun n => (hu n).le
  refine ⟨b, hbC, ?_⟩
  have key : ∀ k : ℕ, ∀ y ∈ C, Θ b + c * (1 - (1 / 2) ^ k) * dist y b ^ 2 ≤ Θ y := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hFb.trans (hle y hy)
    | succ k ih =>
      intro y hy
      have h1 := ih _ (hmem b hbC y hy)
      have h2 := hconv b hbC y hy
      rw [dist_comm _ b, dist_mid_left] at h1
      rw [dist_comm y b, pow_succ]
      nlinarith
  intro y hy
  have h1 : Tendsto (fun k : ℕ => Θ b + c * (1 - (1 / 2 : ℝ) ^ k) * dist y b ^ 2) atTop
      (𝓝 (Θ b + c * (1 - 0) * dist y b ^ 2)) := by
    apply Tendsto.const_add
    apply Tendsto.mul_const
    apply Tendsto.const_mul
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_sub 1
  rw [sub_zero, mul_one] at h1
  exact le_of_tendsto' h1 fun k => key k y hy

/-- The first half of part (c) with weights: points x_i with weights w_i ≥ 0 have a barycenter b, with
∑ w_i|yx_i|² ≥ (∑ w_i)|yb|² + ∑ w_i|bx_i|² for all y. It is the minimizer of y ↦ ∑ w_i|yx_i|² given by lem_toolkit_minimization. -/
theorem lem_toolkit_c_exists {ι : Type*} [Fintype ι] [Nonempty Y] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (x : ι → Y) :
    ∃ b, IsBary w x b := by
  rcases (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hw i).eq_or_lt with h0 | h0
  · have h : ∀ i, w i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i (_ : i ∈ Finset.univ) => hw i).1 h0.symm
      exact this i (Finset.mem_univ i)
    exact ⟨Classical.arbitrary Y, fun y => by simp [h]⟩
  · obtain ⟨b, -, hb⟩ := lem_toolkit_minimization (Y := Y) Set.univ isClosed_univ Set.univ_nonempty
      (fun _ _ _ _ => Set.mem_univ _) (fun y => ∑ i, w i * dist y (x i) ^ 2) (by fun_prop)
      (fun y => Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)) h0
      (by
        intro y _ y' _
        have h : ∀ i, w i * dist (mid y y') (x i) ^ 2 ≤
            w i * dist y (x i) ^ 2 / 2 + w i * dist y' (x i) ^ 2 / 2
              - w i * (dist y y' ^ 2 / 4) := by
          intro i
          have h1 := mul_le_mul_of_nonneg_left (cn y y' (x i)) (hw i)
          rw [dist_comm (x i), dist_comm (x i), dist_comm (x i)] at h1
          linarith
        calc ∑ i, w i * dist (mid y y') (x i) ^ 2
            ≤ ∑ i, (w i * dist y (x i) ^ 2 / 2 + w i * dist y' (x i) ^ 2 / 2
              - w i * (dist y y' ^ 2 / 4)) := Finset.sum_le_sum fun i _ => h i
          _ = _ := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
              ← Finset.sum_div, ← Finset.sum_mul]
            ring)
    exact ⟨b, fun y => hb y (Set.mem_univ y)⟩

/-- **Paper: Lemma lem:toolkit (a).** "For x, v and t ∈ [0,1] exactly one point γ(t) has distances t|xv|, (1−t)|xv| from
them, and |zγ(t)|² ≤ (1−t)|zx|² + t|zv|² − t(1−t)|xv|²." The point is the barycenter of x and v with the weights 1−t and t. -/
theorem lem_toolkit_a (x v : Y) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : ∃ γ : Y,
    (dist x γ = t * dist x v ∧ dist γ v = (1 - t) * dist x v) ∧
    (∀ γ', dist x γ' = t * dist x v → dist γ' v = (1 - t) * dist x v → γ' = γ) ∧
    ∀ z, dist z γ ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z v ^ 2 - t * (1 - t) * dist x v ^ 2 := by
  have : Nonempty Y := ⟨x⟩
  obtain ⟨b, hb⟩ := lem_toolkit_c_exists (Y := Y) (ι := Bool) (fun i => cond i t (1 - t))
    (by intro i; cases i <;> simp <;> linarith) (fun i => cond i v x)
  have hpt : IsPt x v t b := by
    intro z
    have h := hb z
    simp only [Fintype.sum_bool, cond_true, cond_false] at h
    have h2 := dist_triangle x b v
    rw [dist_comm x b] at h2
    have h3 : t * (1 - t) * dist x v ^ 2 ≤ t * (1 - t) * (dist b x + dist b v) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg h0 (by linarith))
      exact pow_le_pow_left₀ dist_nonneg h2 2
    have h4 : 0 ≤ ((1 - t) * dist b x - t * dist b v) ^ 2 := sq_nonneg _
    nlinarith
  exact ⟨b, ⟨hpt.dist_left h0 h1, hpt.dist_right h0 h1⟩, fun _ e1 e2 => hpt.eq_of_dist e1 e2, hpt⟩

/-- Part (a) in the words of the library. -/
theorem lem_toolkit_a_isPt (x v : Y) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : ∃ b, IsPt x v t b := by
  obtain ⟨γ, -, -, h⟩ := lem_toolkit_a x v t h0 h1
  exact ⟨γ, h⟩

/-- A point with the distances of part (a) satisfies its inequality. -/
theorem lem_toolkit_a_of_dist {x v c : Y} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (e1 : dist x c = t * dist x v)
    (e2 : dist c v = (1 - t) * dist x v) : IsPt x v t c := by
  obtain ⟨γ, -, hu, h⟩ := lem_toolkit_a x v t h0 h1
  rw [hu c e1 e2]
  exact h

/-- The first step of the proof of part (b): for the point q at s on [p,p′], insert (a) twice into
t(1−t)|xv|² ≤ (1−t)|xq|² + t|qv|². -/
theorem lem_toolkit_b_box (x v p p' : Y) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (1 - t) * dist x v ^ 2 + s * (1 - s) * dist p p' ^ 2 ≤
      (1 - t) * (1 - s) * dist x p ^ 2 + (1 - t) * s * dist x p' ^ 2
        + t * (1 - s) * dist v p ^ 2 + t * s * dist v p' ^ 2 := by
  obtain ⟨q, -, -, hq⟩ := lem_toolkit_a p p' s hs0 hs1
  have h1 := mul_le_mul_of_nonneg_left (hq x) (show 0 ≤ 1 - t by linarith)
  have h2 := mul_le_mul_of_nonneg_left (hq v) ht0
  have h3 := dist_triangle x q v
  rw [dist_comm q v] at h3
  have h4 : t * (1 - t) * dist x v ^ 2 ≤ t * (1 - t) * (dist x q + dist v q) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dist_nonneg h3 2)
      (mul_nonneg ht0 (by linarith))
  have h5 : 0 ≤ ((1 - t) * dist x q - t * dist v q) ^ 2 := sq_nonneg _
  nlinarith

/-- The second step of the proof of part (b), the choice of the parameter: it gives the first inequality of (b), here as
|x₁x₃|² + |x₂x₄|² ≤ |x₁x₂|² + |x₃x₄|² + 2|x₂x₃||x₁x₄|. -/
theorem lem_toolkit_b_first (x₁ x₂ x₃ x₄ : Y) :
    dist x₁ x₃ ^ 2 + dist x₂ x₄ ^ 2 ≤
      dist x₁ x₂ ^ 2 + dist x₃ x₄ ^ 2 + 2 * dist x₂ x₃ * dist x₁ x₄ := by
  have key : dist x₁ x₃ ^ 2 + dist x₂ x₄ ^ 2 - dist x₁ x₂ ^ 2 - dist x₃ x₄ ^ 2 ≤
      2 * dist x₁ x₄ * dist x₂ x₃ := by
    apply le_two_mul_of_forall dist_nonneg dist_nonneg
    intro τ hτ
    have hs0 : 0 ≤ τ / (1 + τ) := by positivity
    have hs1 : τ / (1 + τ) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have h := lem_toolkit_b_box x₁ x₃ x₄ x₂ hs0 hs1 hs0 hs1
    have e1 : 1 - τ / (1 + τ) = 1 / (1 + τ) := by field_simp; ring
    rw [e1] at h
    have hpos : 0 < (1 + τ) ^ 2 / τ := by positivity
    have h2 := mul_le_mul_of_nonneg_left h hpos.le
    have e2 : (1 + τ) ^ 2 / τ * (τ / (1 + τ) * (1 / (1 + τ)) * dist x₁ x₃ ^ 2 +
        τ / (1 + τ) * (1 / (1 + τ)) * dist x₄ x₂ ^ 2) =
        dist x₁ x₃ ^ 2 + dist x₄ x₂ ^ 2 := by field_simp
    have e3 : (1 + τ) ^ 2 / τ * (1 / (1 + τ) * (1 / (1 + τ)) * dist x₁ x₄ ^ 2 +
        1 / (1 + τ) * (τ / (1 + τ)) * dist x₁ x₂ ^ 2 +
        τ / (1 + τ) * (1 / (1 + τ)) * dist x₃ x₄ ^ 2 +
        τ / (1 + τ) * (τ / (1 + τ)) * dist x₃ x₂ ^ 2) =
        dist x₁ x₄ ^ 2 / τ + dist x₁ x₂ ^ 2 + dist x₃ x₄ ^ 2 + τ * dist x₃ x₂ ^ 2 := by
      field_simp
    rw [e2, e3, dist_comm x₄ x₂, dist_comm x₃ x₂] at h2
    linarith
  linarith

/-- **Paper: Lemma lem:toolkit (b).** "|xv|² + |yu|² ≤ |xu|² + |yv|² + 2|xy||uv|; in particular the squared diagonals of a
quadrangle add up to at most its squared sides, and if there is equality, opposite sides are equal." -/
theorem lem_toolkit_b (x v y u : Y) :
    dist x v ^ 2 + dist y u ^ 2 ≤ dist x u ^ 2 + dist y v ^ 2 + 2 * dist x y * dist u v ∧
    dist x v ^ 2 + dist y u ^ 2 ≤ dist x y ^ 2 + dist y v ^ 2 + dist v u ^ 2 + dist x u ^ 2 ∧
    (dist x v ^ 2 + dist y u ^ 2 = dist x y ^ 2 + dist y v ^ 2 + dist v u ^ 2 + dist x u ^ 2 →
      dist x y = dist v u ∧ dist y v = dist x u) := by
  have h1 : dist x v ^ 2 + dist y u ^ 2 ≤ dist x u ^ 2 + dist y v ^ 2 + 2 * dist x y * dist u v := by
    have h := lem_toolkit_b_first x u v y
    rw [dist_comm u y, dist_comm v y] at h
    linarith
  have h2 : dist x v ^ 2 + dist y u ^ 2 ≤ dist x y ^ 2 + dist v u ^ 2 + 2 * dist y v * dist x u :=
    lem_toolkit_b_first x y v u
  refine ⟨h1, by nlinarith [sq_nonneg (dist y v - dist x u)], fun he => ⟨?_, ?_⟩⟩
  · have h3 : (dist x y - dist v u) ^ 2 ≤ 0 := by
      rw [dist_comm u v] at h1
      nlinarith
    have h4 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _))
    linarith
  · have h3 : (dist y v - dist x u) ^ 2 ≤ 0 := by nlinarith
    have h4 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _))
    linarith

/-- The second half of part (c) with weights: (∑ w_i)|bb′| ≤ ∑ w_i|x_ix′_i|. "Adding the inequality of (c) for (b,x) at b′
and for (b′,x′) at b, and applying (b) to every b, b′, x_i, x′_i". -/
theorem lem_toolkit_c_contract {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {x x' : ι → Y} {b b' : Y}
    (h : IsBary w x b) (h' : IsBary w x' b') :
    (∑ i, w i) * dist b b' ≤ ∑ i, w i * dist (x i) (x' i) := by
  rcases (dist_nonneg (x := b) (y := b')).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) dist_nonneg
  have h1 := h b'
  have h2 := h' b
  rw [dist_comm b' b] at h1
  have h3 : ∀ i, w i * dist b' (x i) ^ 2 + w i * dist b (x' i) ^ 2 ≤
      w i * dist b (x i) ^ 2 + w i * dist b' (x' i) ^ 2
        + 2 * dist b b' * (w i * dist (x i) (x' i)) := by
    intro i
    have h4 := mul_le_mul_of_nonneg_left (lem_toolkit_b b' (x i) b (x' i)).1 (hw i)
    rw [dist_comm (x' i) (x i), dist_comm b' b] at h4
    linarith
  have h5 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h3 i
  simp only [Finset.sum_add_distrib] at h5
  rw [← Finset.mul_sum] at h5
  have h6 : dist b b' * ((∑ i, w i) * dist b b') ≤
      dist b b' * ∑ i, w i * dist (x i) (x' i) := by nlinarith
  exact le_of_mul_le_mul_left h6 h0

/-- **Paper: Lemma lem:toolkit (c).** "Points x₁, …, x_n, n ≥ 1, have a barycenter b, the minimizer of y ↦ ∑|yx_i|², with
∑|yx_i|² ≥ n|yb|² + ∑|bx_i|² for all y; if b′ is that of x′₁, …, x′_n, then n|bb′| ≤ ∑|x_ix′_i|." Here a barycenter is a
point with the displayed inequality; by lem_toolkit_c_minimizer this is the same as being the minimizer, and there is exactly
one. -/
theorem lem_toolkit_c :
    (∀ (n : ℕ) (x : Fin n → Y), 0 < n → ∃ b, ∀ y,
      (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) ∧
    ∀ (n : ℕ) (x x' : Fin n → Y) (b b' : Y),
      (∀ y, (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) →
      (∀ y, (n : ℝ) * dist y b' ^ 2 + ∑ i, dist b' (x' i) ^ 2 ≤ ∑ i, dist y (x' i) ^ 2) →
      (n : ℝ) * dist b b' ≤ ∑ i, dist (x i) (x' i) := by
  constructor
  · intro n x hn
    have : Nonempty Y := ⟨x ⟨0, hn⟩⟩
    obtain ⟨b, hb⟩ := lem_toolkit_c_exists (fun _ : Fin n => (1 : ℝ)) (fun _ => zero_le_one) x
    refine ⟨b, fun y => ?_⟩
    have := hb y
    simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
    linarith
  · intro n x x' b b' hb hb'
    have conv : ∀ (x : Fin n → Y) (b : Y),
        (∀ y, (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) →
          IsBary (fun _ => (1 : ℝ)) x b := by
      intro x b h y
      simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      linarith [h y]
    simpa using lem_toolkit_c_contract (fun _ => zero_le_one) (conv x b hb) (conv x' b' hb')

/-- Part (c): the barycenter is "the minimizer of y ↦ ∑|yx_i|²". For n ≥ 1 there is exactly one minimizer, and a point is the
minimizer if and only if it satisfies the inequality of (c), by which lem_toolkit_c describes the barycenter. -/
theorem lem_toolkit_c_minimizer {n : ℕ} (hn : 0 < n) (x : Fin n → Y) :
    (∃! b, ∀ y, ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) ∧
    ∀ b, (∀ y, (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) ↔
      ∀ y, ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨b₀, h₀⟩ := lem_toolkit_c.1 n x hn
  have hmin : ∀ b, (∀ y, (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) →
      ∀ y, ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2 := fun b h y => by
    nlinarith [h y, sq_nonneg (dist y b)]
  have huniq : ∀ b, (∀ y, ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) → b = b₀ := fun b h => by
    have h1 : (n : ℝ) * dist b b₀ ^ 2 ≤ 0 := by linarith [h₀ b, h b₀]
    have h2 : dist b b₀ ^ 2 ≤ 0 := by nlinarith
    exact dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h2 (sq_nonneg _)))
  exact ⟨⟨b₀, hmin b₀ h₀, huniq⟩, fun b => ⟨hmin b, fun h => (huniq b h).symm ▸ h₀⟩⟩

/-- **Paper: Lemma lem:toolkit (d).** "A nonempty closed convex F has nearest points Py, with |yq|² ≥ |yPy|² + |Py,q|² for
q ∈ F." A set is convex if it contains the midpoints of its points. -/
theorem lem_toolkit_d (F : Set Y) (hF : IsClosed F) (hne : F.Nonempty)
    (hconv : ∀ x ∈ F, ∀ v ∈ F, ∀ m, dist x m = dist x v / 2 → dist m v = dist x v / 2 → m ∈ F) (y : Y) :
    ∃ P ∈ F, (∀ q ∈ F, dist y P ≤ dist y q) ∧ ∀ q ∈ F, dist y P ^ 2 + dist P q ^ 2 ≤ dist y q ^ 2 := by
  obtain ⟨P, hP, h⟩ := lem_toolkit_minimization F hF hne
    (fun x hx v hv => hconv x hx v hv _ (dist_mid_left x v) (dist_mid_right x v))
    (fun q => dist y q ^ 2) (by fun_prop) (fun _ => sq_nonneg _) one_pos
    (fun x _ v _ => by linarith [cn x v y])
  have h' : ∀ q ∈ F, dist y P ^ 2 + dist P q ^ 2 ≤ dist y q ^ 2 := fun q hq => by
    have := h q hq
    rw [dist_comm P q]
    linarith
  exact ⟨P, hP, fun q hq => (abs_le_of_sq_le_sq' (by nlinarith [h' q hq]) dist_nonneg).2, h'⟩

/-- Part (e) for factors that may differ. -/
theorem lem_toolkit_e_general {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MetricSpace (X i)] [∀ i, CN (X i)] :
    CN (PiLp 2 X) where
  exists_mid x v := by
    refine ⟨WithLp.toLp 2 fun i => mid (x i) (v i), fun z => ?_⟩
    simp only [piLp_dist_sq]
    calc ∑ i, dist (z i) (mid (x i) (v i)) ^ 2
        ≤ ∑ i, ((dist (z i) (x i) ^ 2 + dist (z i) (v i) ^ 2) / 2
          - dist (x i) (v i) ^ 2 / 4) := Finset.sum_le_sum fun i _ => cn _ _ _
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, Finset.sum_add_distrib]

/-- **Paper: Lemma lem:toolkit (e).** "Finite L² products of copies of Y are CAT(0)." -/
theorem lem_toolkit_e (ι : Type) [Fintype ι] : CN (PiLp 2 fun _ : ι => Y) := lem_toolkit_e_general

/-! Part (f). The letters are those of the paper: |xy| = |uv| = δ, |xu| = |yv| = h, a is the point at s on [x,u] and b the
point at t on [y,v]. The steps before the last one ask only that the squared diagonals add up to at least 2h² + 2δ² (a flat
parallelogram). The form Φ(p,p′;r,r′) = |pr′|² + |p′r|² − |pr|² − |p′r′|² is at most 2|pp′||rr′| by (b), and it is additive when
[p,p′] and [r,r′] are cut; so equality for the whole is inherited by the parts. -/

/-- Φ(p,p′;r,r′) ≤ 2|pp′||rr′|, by part (b). -/
theorem lem_toolkit_f_form (p p' r r' : Y) :
    dist p r' ^ 2 + dist p' r ^ 2 - dist p r ^ 2 - dist p' r' ^ 2 ≤ 2 * dist p p' * dist r r' := by
  linarith [(lem_toolkit_b p r' p' r).1]

/-- The form is additive, Φ(x,u;y,v) = Φ(x,a;y,b) + Φ(x,a;b,v) + Φ(a,u;y,b) + Φ(a,u;b,v), and the four bounds of
lem_toolkit_f_form add up to 2h², which is at most Φ(x,u;y,v) by hypothesis. So all four are equalities; the first one says
|xb|² + |ay|² − δ² − |ab|² = 2sth². -/
theorem lem_toolkit_f_parts {x u v y a b : Y} {h δ s t : ℝ} (hp : dist x u = h) (hp' : dist y v = h)
    (hq : dist u v = δ) (hq' : dist x y = δ)
    (hd : 2 * h ^ 2 + 2 * δ ^ 2 ≤ dist x v ^ 2 + dist u y ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : IsPt x u s a) (hb : IsPt y v t b) :
    dist x b ^ 2 + dist a y ^ 2 - δ ^ 2 - dist a b ^ 2 = 2 * s * t * h ^ 2 := by
  have e1 := ha.dist_left hs0 hs1
  have e2 := ha.dist_right hs0 hs1
  have e3 := hb.dist_left ht0 ht1
  have e4 := hb.dist_right ht0 ht1
  rw [hp] at e1 e2
  rw [hp'] at e3 e4
  have f1 := lem_toolkit_f_form x a y b
  have f2 := lem_toolkit_f_form x a b v
  have f3 := lem_toolkit_f_form a u y b
  have f4 := lem_toolkit_f_form a u b v
  rw [e1, e3, hq'] at f1
  rw [e1, e4] at f2
  rw [e2, e3] at f3
  rw [e2, e4, hq] at f4
  nlinarith

/-- The case s = t: then |ab| = δ, and |xb|² and |ay|² have the values that the inequality of (a) allows at most. -/
theorem lem_toolkit_f_same {x u v y a b : Y} {h δ s : ℝ} (hp : dist x u = h) (hp' : dist y v = h)
    (hq : dist u v = δ) (hq' : dist x y = δ)
    (hd : 2 * h ^ 2 + 2 * δ ^ 2 ≤ dist x v ^ 2 + dist u y ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha : IsPt x u s a) (hb : IsPt y v s b) :
    dist a b = δ ∧ dist x b ^ 2 = (1 - s) * δ ^ 2 + s * dist x v ^ 2 - s * (1 - s) * h ^ 2 ∧
      dist a y ^ 2 = (1 - s) * δ ^ 2 + s * dist u y ^ 2 - s * (1 - s) * h ^ 2 := by
  have h1 := lem_toolkit_f_parts hp hp' hq hq' hd hs0 hs1 hs0 hs1 ha hb
  have h2 := lem_toolkit_b_first x a b y
  have e1 := ha.dist_left hs0 hs1
  have e3 := hb.dist_left hs0 hs1
  rw [hp] at e1
  rw [hp'] at e3
  rw [dist_comm b y, e1, e3, hq'] at h2
  have h3 : (dist a b - δ) ^ 2 ≤ 0 := by nlinarith
  have h4 : dist a b = δ := by
    have : dist a b - δ = 0 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _))
    linarith
  have h5 := hb x
  have h6 := ha y
  rw [hp', hq'] at h5
  rw [hp, dist_comm y a, dist_comm y x, dist_comm y u, hq'] at h6
  have h7 := (lem_toolkit_b x v u y).2.1
  rw [hp, hq, hq', dist_comm v y, hp'] at h7
  rw [h4] at h1
  have h8 : dist x v ^ 2 + dist u y ^ 2 = 2 * h ^ 2 + 2 * δ ^ 2 := le_antisymm (by linarith) hd
  have h9 : s * dist x v ^ 2 + s * dist u y ^ 2 = s * (2 * h ^ 2 + 2 * δ ^ 2) := by
    rw [← mul_add, h8]
  refine ⟨h4, ?_, ?_⟩ <;> nlinarith

/-- The values of |xb|² and |ay|² from lem_toolkit_f_same, inserted into lem_toolkit_f_parts: the formula for |ab|², still in
terms of the two diagonals. -/
theorem lem_toolkit_f_parallelogram {x u v y a b : Y} {h δ s t : ℝ} (hp : dist x u = h) (hp' : dist y v = h)
    (hq : dist u v = δ) (hq' : dist x y = δ)
    (hd : 2 * h ^ 2 + 2 * δ ^ 2 ≤ dist x v ^ 2 + dist u y ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : IsPt x u s a) (hb : IsPt y v t b) :
    dist a b ^ 2 = (1 - s - t) * δ ^ 2 + t * dist x v ^ 2 + s * dist u y ^ 2
      - s * (1 - s) * h ^ 2 - t * (1 - t) * h ^ 2 - 2 * s * t * h ^ 2 := by
  have h1 := lem_toolkit_f_parts hp hp' hq hq' hd hs0 hs1 ht0 ht1 ha hb
  obtain ⟨a', ha'⟩ := lem_toolkit_a_isPt x u ht0 ht1
  obtain ⟨b', hb'⟩ := lem_toolkit_a_isPt y v hs0 hs1
  have h2 := (lem_toolkit_f_same hp hp' hq hq' hd ht0 ht1 ha' hb).2.1
  have h3 := (lem_toolkit_f_same hp hp' hq hq' hd hs0 hs1 ha hb').2.2
  rw [h2, h3] at h1
  linarith

/-- Part (f), with a ∈ [x,u] and b ∈ [y,v] given by the inequality of (a) (Cat.IsPt), and with lower bounds for the diagonals. -/
theorem lem_toolkit_f_isPt {x u v y a b : Y} {h δ s t : ℝ} (hp : dist x u = h) (hp' : dist y v = h)
    (hq : dist u v = δ) (hq' : dist x y = δ)
    (hd : h ^ 2 + δ ^ 2 ≤ dist x v ^ 2) (hd' : h ^ 2 + δ ^ 2 ≤ dist u y ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : IsPt x u s a) (hb : IsPt y v t b) :
    dist a b ^ 2 = δ ^ 2 + (s - t) ^ 2 * h ^ 2 := by
  have hab := lem_toolkit_f_parallelogram hp hp' hq hq' (by linarith) hs0 hs1 ht0 ht1 ha hb
  have h7 := (lem_toolkit_b x v u y).2.1
  rw [hp, hq, hq', dist_comm v y, hp'] at h7
  have h8 : dist x v ^ 2 = h ^ 2 + δ ^ 2 := by linarith
  have h9 : dist u y ^ 2 = h ^ 2 + δ ^ 2 := by linarith
  rw [hab, h8, h9]
  ring

/-- **Paper: Lemma lem:toolkit (f).** "Flat rectangles: if |xy| = |uv| = δ, |xu| = |yv| = h and both diagonals have squared
length δ² + h², and a ∈ [x,u], b ∈ [y,v] have |xa| = sh, |yb| = th, then |ab|² = δ² + h²(s−t)²." -/
theorem lem_toolkit_f (x y u v a b : Y) (δ h s t : ℝ) (hxy : dist x y = δ) (huv : dist u v = δ) (hxu : dist x u = h)
    (hyv : dist y v = h) (d1 : dist x v ^ 2 = δ ^ 2 + h ^ 2) (d2 : dist y u ^ 2 = δ ^ 2 + h ^ 2) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a1 : dist x a = s * dist x u) (a2 : dist a u = (1 - s) * dist x u)
    (b1 : dist y b = t * dist y v) (b2 : dist b v = (1 - t) * dist y v) :
    dist a b ^ 2 = δ ^ 2 + h ^ 2 * (s - t) ^ 2 := by
  have := lem_toolkit_f_isPt (x := x) (u := u) (y := y) (v := v) (a := a) (b := b) hxu hyv huv hxy
    (by linarith) (by rw [dist_comm u y]; linarith) hs0 hs1 ht0 ht1 (lem_toolkit_a_of_dist hs0 hs1 a1 a2)
    (lem_toolkit_a_of_dist ht0 ht1 b1 b2)
  linarith

end Toolkit

open Cat in
/-- **Paper: Lemma lem:toolkit.** "Let Y be CAT(0). (a) For x, v and t ∈ [0,1] exactly one point γ(t) has distances t|xv|,
(1−t)|xv| from them, and |zγ(t)|² ≤ (1−t)|zx|² + t|zv|² − t(1−t)|xv|². (b) |xv|² + |yu|² ≤ |xu|² + |yv|² + 2|xy||uv|; in
particular the squared diagonals of a quadrangle add up to at most its squared sides, and if there is equality, opposite sides
are equal. (c) Points x₁, …, x_n, n ≥ 1, have a barycenter b, the minimizer of y ↦ ∑|yx_i|², with
∑|yx_i|² ≥ n|yb|² + ∑|bx_i|² for all y; if b′ is that of x′₁, …, x′_n, then n|bb′| ≤ ∑|x_ix′_i|. (d) A nonempty closed
convex F has nearest points Py, with |yq|² ≥ |yPy|² + |Py,q|² for q ∈ F. (e) Finite L² products of copies of Y are CAT(0).
(f) Flat rectangles: if |xy| = |uv| = δ, |xu| = |yv| = h and both diagonals have squared length δ² + h², and a ∈ [x,u],
b ∈ [y,v] have |xa| = sh, |yb| = th, then |ab|² = δ² + h²(s−t)²." In (c) a barycenter is a point with the displayed
inequality; by lem_toolkit_c_minimizer this is the same as being the minimizer, and there is exactly one. -/
theorem lem_toolkit {Y : Type} [MetricSpace Y] [CN Y] :
    (∀ (x v : Y) (t : ℝ), 0 ≤ t → t ≤ 1 → ∃ γ : Y,
      (dist x γ = t * dist x v ∧ dist γ v = (1 - t) * dist x v) ∧
      (∀ γ', dist x γ' = t * dist x v → dist γ' v = (1 - t) * dist x v → γ' = γ) ∧
      ∀ z, dist z γ ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z v ^ 2 - t * (1 - t) * dist x v ^ 2) ∧
    (∀ x v y u : Y,
      dist x v ^ 2 + dist y u ^ 2 ≤ dist x u ^ 2 + dist y v ^ 2 + 2 * dist x y * dist u v ∧
      dist x v ^ 2 + dist y u ^ 2 ≤ dist x y ^ 2 + dist y v ^ 2 + dist v u ^ 2 + dist x u ^ 2 ∧
      (dist x v ^ 2 + dist y u ^ 2 = dist x y ^ 2 + dist y v ^ 2 + dist v u ^ 2 + dist x u ^ 2 →
        dist x y = dist v u ∧ dist y v = dist x u)) ∧
    ((∀ (n : ℕ) (x : Fin n → Y), 0 < n → ∃ b, ∀ y,
        (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) ∧
      ∀ (n : ℕ) (x x' : Fin n → Y) (b b' : Y),
        (∀ y, (n : ℝ) * dist y b ^ 2 + ∑ i, dist b (x i) ^ 2 ≤ ∑ i, dist y (x i) ^ 2) →
        (∀ y, (n : ℝ) * dist y b' ^ 2 + ∑ i, dist b' (x' i) ^ 2 ≤ ∑ i, dist y (x' i) ^ 2) →
        (n : ℝ) * dist b b' ≤ ∑ i, dist (x i) (x' i)) ∧
    (∀ F : Set Y, IsClosed F → F.Nonempty →
      (∀ x ∈ F, ∀ v ∈ F, ∀ m, dist x m = dist x v / 2 → dist m v = dist x v / 2 → m ∈ F) →
      ∀ y, ∃ P ∈ F, (∀ q ∈ F, dist y P ≤ dist y q) ∧ ∀ q ∈ F, dist y P ^ 2 + dist P q ^ 2 ≤ dist y q ^ 2) ∧
    (∀ (ι : Type) [Fintype ι], CN (PiLp 2 fun _ : ι => Y)) ∧
    ∀ (x y u v a b : Y) (δ h s t : ℝ), dist x y = δ → dist u v = δ → dist x u = h → dist y v = h →
      dist x v ^ 2 = δ ^ 2 + h ^ 2 → dist y u ^ 2 = δ ^ 2 + h ^ 2 → 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      dist x a = s * dist x u → dist a u = (1 - s) * dist x u →
      dist y b = t * dist y v → dist b v = (1 - t) * dist y v →
      dist a b ^ 2 = δ ^ 2 + h ^ 2 * (s - t) ^ 2 :=
  ⟨lem_toolkit_a, lem_toolkit_b, lem_toolkit_c, lem_toolkit_d, fun ι _ => lem_toolkit_e ι, lem_toolkit_f⟩

end Paper

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
section
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
end

namespace Paper
open Finset Filter Topology Nc.Price Nc.Flag
variable {μ : ℕ}
theorem meanSq_nonneg (w : Mt μ → Mt μ → ℝ) (r : ℕ) : 0 ≤ meanSq w r :=
  div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

theorem rank_units (p q : GLM (Fin μ)) (W : Mt μ) : ((p : Mt μ) * W * (q : Mt μ)).rank = W.rank := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 q.isUnit),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 p.isUnit)]

theorem rank_dg (S : Finset (Fin μ)) : (dg S : Mt μ).rank = S.card := by
  rw [dg, Matrix.rank_diagonal, Fintype.card_subtype]
  congr 1
  ext i
  simp

/-- The sum of f(p·dg(S)·q)² over all invertible p and q (this is `DM f (dg S)`), divided by the number of these pairs, is the
mean of f(W)² over the matrices W of rank |S|. -/
theorem card_mul_DM (f : Mt μ → ℝ) (S : Finset (Fin μ)) :
    (((univ : Finset (Mt μ)).filter fun W => W.rank = S.card).card : ℝ) * DM f (dg S) =
      (Fintype.card (GLM (Fin μ)) : ℝ) ^ 2 *
        ∑ W ∈ (univ : Finset (Mt μ)).filter (fun W => W.rank = S.card), f W ^ 2 := by
  have h1 : ∀ W ∈ (univ : Finset (Mt μ)).filter (fun W => W.rank = S.card), DM f W = DM f (dg S) := by
    intro W hW
    obtain ⟨p, q, T, rfl⟩ := exists_factor W
    rw [mem_filter, rank_units, rank_dg] at hW
    rw [DM_mul, DM_dg_congr f hW.2]
  have h2 : ∀ p q : GLM (Fin μ), ∑ W ∈ (univ : Finset (Mt μ)).filter (fun W => W.rank = S.card),
      f ((p : Mt μ) * W * (q : Mt μ)) ^ 2 =
        ∑ W ∈ (univ : Finset (Mt μ)).filter (fun W => W.rank = S.card), f W ^ 2 := by
    intro p q
    rw [sum_filter, sum_filter]
    let E : Mt μ ≃ Mt μ := (Units.mulLeft p).trans (Units.mulRight q)
    refine Eq.trans (sum_congr rfl fun W _ => ?_) (Equiv.sum_comp E fun W => if W.rank = S.card then f W ^ 2 else 0)
    show _ = if ((p : Mt μ) * W * (q : Mt μ)).rank = S.card then f ((p : Mt μ) * W * (q : Mt μ)) ^ 2 else 0
    rw [rank_units]
  rw [← nsmul_eq_mul, ← sum_const, ← sum_congr rfl h1]
  unfold DM
  rw [sum_comm, sum_congr rfl fun p _ => sum_comm, sum_congr rfl fun p _ => sum_congr rfl fun q _ => h2 p q]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  ring


end Paper

namespace Paper
private theorem prop_space {K : Type} [Field K] {V : Type} {w : V → V → ℝ} (hw : Nc.Price.IsPrice K w) :
    ∃ (X : Type) (_ : MetricSpace X) (_ : Cat.CN X) (f : V → X),
      Nc.Price.IsPrice K (fun a b : X => dist a b) ∧ ∀ a b, dist (f a) (f b) = w a b := by
  obtain ⟨X, hX, f, hc, hmid, hprice, hiso⟩ := ValiantBorder.priceMetricRealization hw
  letI := hX
  exact ⟨X, hX, (cat0_iff X).mpr ⟨hc, hmid⟩, f, hprice, hiso⟩
end Paper

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Finite groups of isometries of complete CAT(0) spaces: projections to fixed points
-/

open Finset

namespace Nc.Flag

open Cat

/-- An action by isometries. -/
structure IsoAct (G Z : Type*) [Group G] [MetricSpace Z] where
  /-- the action -/
  act : G → Z → Z
  one' : ∀ z, act 1 z = z
  mul' : ∀ g h z, act (g * h) z = act g (act h z)
  iso' : ∀ g z z', dist (act g z) (act g z') = dist z z'

namespace IsoAct
variable {G H Z : Type*} [Group G] [Group H] [MetricSpace Z] (A : IsoAct G Z)

/-- Pull-back along a homomorphism. -/
def comap (φ : H →* G) : IsoAct H Z where
  act g := A.act (φ g)
  one' z := by rw [map_one, A.one']
  mul' g h z := by rw [map_mul, A.mul']
  iso' g := A.iso' _

theorem isometry (g : G) : Isometry (A.act g) := Isometry.of_dist_eq (A.iso' g)

theorem surj (g : G) : Function.Surjective (A.act g) := fun z =>
  ⟨A.act g⁻¹ z, by rw [← A.mul', mul_inv_cancel, A.one']⟩

/-- The displacement of a point. -/
def len (z : Z) : Len G where
  val g := dist z (A.act g z)
  one' := by rw [A.one', dist_self]
  inv' g := by
    rw [← A.iso' g, ← A.mul', mul_inv_cancel, A.one', dist_comm]
  mul' g h := by
    rw [A.mul']
    refine (dist_triangle z (A.act g z) _).trans ?_
    rw [A.iso']

theorem len_val (z : Z) (g : G) : (A.len z).val g = dist z (A.act g z) := rfl

/-- Fixed points. -/
def Fix (z : Z) : Prop := ∀ g, A.act g z = z

section proj
variable [CN Z] [Fintype G]

theorem exists_proj (z : Z) : ∃ b, IsBary (fun _ : G => (1 : ℝ)) (fun g => A.act g z) b := by
  have : Nonempty Z := ⟨z⟩
  exact Paper.lem_toolkit_c_exists _ (fun _ => zero_le_one) _

/-- The projection to the fixed points: the barycentre of the orbit. -/
noncomputable def P (z : Z) : Z := Classical.choose (A.exists_proj z)

theorem P_spec (z : Z) : IsBary (fun _ : G => (1 : ℝ)) (fun g => A.act g z) (A.P z) :=
  Classical.choose_spec (A.exists_proj z)

theorem card_pos' : (0 : ℝ) < ∑ _g : G, (1 : ℝ) := by
  rw [sum_const, card_univ, nsmul_eq_mul, mul_one]
  exact_mod_cast Fintype.card_pos

/-- An isometry that commutes with the action commutes with the projection. -/
theorem P_comm (f : Z → Z) (hf : Isometry f) (hs : Function.Surjective f)
    (hc : ∀ g z, f (A.act g z) = A.act g (f z)) (z : Z) : f (A.P z) = A.P (f z) := by
  have h1 := (A.P_spec z).map hf hs
  simp only [hc] at h1
  exact h1.unique card_pos' (A.P_spec (f z))

theorem P_fix (z : Z) : A.Fix (A.P z) := by
  intro g
  have h1 := (A.P_spec z).map (A.isometry g) (A.surj g)
  have h2 := (A.P_spec z).comp_equiv (Equiv.mulLeft g)
  refine h1.unique card_pos' ?_
  have e : (fun i => A.act g (A.act i z)) = (fun g => A.act g z) ∘ Equiv.mulLeft g :=
    funext fun k => (A.mul' g k z).symm
  rw [e]
  exact h2

end proj
end IsoAct

/-- The arithmetic at the end of the proof of Lemma lem:angle (a quadrangle with two right angles). -/
theorem angle_num {r r' α β Q A c : ℝ} (hr : 0 < r) (hr' : 0 < r') (hα : 0 < α) (hβ : 0 < β)
    (hA1 : r ^ 2 + α ^ 2 ≤ A) (hA2 : r' ^ 2 + β ^ 2 ≤ A)
    (hQ : α ^ 2 + β ^ 2 - 2 * c * (α * β) ≤ Q)
    (hbox : ∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      t * (1 - t) * A + s * (1 - s) * Q ≤ (1 - t) * (1 - s) * r ^ 2 + (1 - t) * s * r' ^ 2 +
        t * (1 - s) * α ^ 2 + t * s * β ^ 2) :
    Q ≤ r ^ 2 + r' ^ 2 + 2 * c * (r * r') := by
  set T := r * α + r' * β with hT
  set S := r * β + r' * α with hS
  set N := r * r' + α * β with hN
  have hT0 : 0 < T := by positivity
  have hN0 : 0 < N := by positivity
  set s := r * α / T with hs
  set t := r * r' / N with ht
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by
    rw [hs, div_le_one hT0, hT]
    have : 0 ≤ r' * β := by positivity
    linarith
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one hN0, hN]
    have : 0 ≤ α * β := by positivity
    linarith
  have hb := hbox s t hs0 hs1 ht0 ht1
  have hA : (1 - s) * (r ^ 2 + α ^ 2) + s * (r' ^ 2 + β ^ 2) ≤ A := by
    have h1 := mul_le_mul_of_nonneg_left hA1 (show 0 ≤ 1 - s by linarith)
    have h2 := mul_le_mul_of_nonneg_left hA2 hs0
    linarith
  have hA' := mul_le_mul_of_nonneg_left hA (show 0 ≤ t * (1 - t) from
    mul_nonneg ht0 (by linarith))
  have h1 : s * (1 - s) * Q ≤ (1 - t) ^ 2 * ((1 - s) * r ^ 2 + s * r' ^ 2) +
      t ^ 2 * ((1 - s) * α ^ 2 + s * β ^ 2) := by nlinarith
  have e1 : 1 - s = r' * β / T := by rw [hs, hT]; field_simp; ring
  have e2 : 1 - t = α * β / N := by rw [ht, hN]; field_simp; ring
  have e3 : (1 - s) * r ^ 2 + s * r' ^ 2 = r * r' * S / T := by
    rw [e1, hs, hS]; field_simp
  have e4 : (1 - s) * α ^ 2 + s * β ^ 2 = α * β * S / T := by
    rw [e1, hs, hS]; field_simp; ring
  have e5 : (1 - t) ^ 2 * (r * r' * S / T) + t ^ 2 * (α * β * S / T) =
      (r * r' * (α * β)) * (S / (T * N)) := by
    rw [e2, ht]
    field_simp
    rw [hN]; ring
  have e6 : s * (1 - s) = (r * r' * (α * β)) * (1 / T ^ 2) := by
    rw [e1, hs]; field_simp
  rw [e3, e4, e5, e6, mul_assoc] at h1
  have h2 := le_of_mul_le_mul_left h1 (by positivity)
  have h3 : Q * N ≤ T * S := by
    have h4 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ T ^ 2 * N by positivity)
    have e7 : T ^ 2 * N * (1 / T ^ 2 * Q) = Q * N := by field_simp
    have e8 : T ^ 2 * N * (S / (T * N)) = T * S := by field_simp
    rw [e7, e8] at h4
    exact h4
  have e9 : T * S = α * β * (r ^ 2 + r' ^ 2) + r * r' * (α ^ 2 + β ^ 2) := by
    rw [hT, hS]; ring
  have h4 : r * r' * (α ^ 2 + β ^ 2) ≤ r * r' * (Q + 2 * c * (α * β)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [e9, hN] at h3
  have h5 : (α * β) * Q ≤ (α * β) * (r ^ 2 + r' ^ 2 + 2 * c * (r * r')) := by nlinarith
  exact le_of_mul_le_mul_left h5 (by positivity)

end Nc.Flag

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Blow-ups `N ↦ N ⊗ 1` of matrices over F₂
-/

open Finset Matrix

namespace Nc.Flag

variable {μ κ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype κ] [DecidableEq κ]
  [Fintype ι] [DecidableEq ι]

/-- The inclusion matrix of an embedding. -/
def inc (e : μ × κ ↪ ι) : Matrix ι (μ × κ) F2 := fun i x => if i = e x then 1 else 0

theorem inc_t_mul (e : μ × κ ↪ ι) : (inc e)ᵀ * inc e = 1 := by
  ext x y
  simp [Matrix.mul_apply, inc, Matrix.one_apply, eq_comm]

theorem inc_mul_diag (e : μ × κ ↪ ι) (T : Finset (μ × κ)) :
    inc e * dg T * (inc e)ᵀ = dg (T.map e) := by
  ext i j
  simp only [Matrix.mul_apply, inc, dg, Matrix.transpose_apply, Matrix.diagonal_apply,
    Finset.mem_map]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  by_cases hi : ∃ x, e x = i
  · obtain ⟨x, rfl⟩ := hi
    by_cases hj : ∃ y, e y = j
    · obtain ⟨y, rfl⟩ := hj
      by_cases hxy : x = y
      · subst hxy
        simp [e.injective.eq_iff]
      · simp [e.injective.eq_iff, hxy]
    · have : ∀ y, j ≠ e y := fun y h => hj ⟨y, h.symm⟩
      have h2 : e x ≠ j := fun h => hj ⟨x, h⟩
      simp [this, h2]
  · have h1 : ∀ y, i ≠ e y := fun y h => hi ⟨y, h.symm⟩
    have h2 : ∀ y, e y ≠ i := fun y h => hi ⟨y, h⟩
    simp only [h1, if_false, sum_const_zero, ite_self]
    split_ifs with h3 h4
    · obtain ⟨a, -, ha⟩ := h4
      exact absurd ha (h2 a)
    · rfl
    · rfl

/-- The blow-up of a matrix along an embedding. -/
def blow (e : μ × κ ↪ ι) (N : Matrix μ μ F2) : Matrix ι ι F2 :=
  inc e * (Matrix.kroneckerMap (· * ·) N (1 : Matrix κ κ F2)) * (inc e)ᵀ

theorem blow_add (e : μ × κ ↪ ι) (M N : Matrix μ μ F2) :
    blow e (M + N) = blow e M + blow e N := by
  unfold blow
  rw [Matrix.add_kronecker, Matrix.mul_add, Matrix.add_mul]

theorem blow_mul (e : μ × κ ↪ ι) (M N : Matrix μ μ F2) :
    blow e (M * N) = blow e M * blow e N := by
  unfold blow
  have h : Matrix.kroneckerMap (· * ·) (M * N) (1 : Matrix κ κ F2) =
      Matrix.kroneckerMap (· * ·) M (1 : Matrix κ κ F2) *
        Matrix.kroneckerMap (· * ·) N (1 : Matrix κ κ F2) := by
    have := Matrix.mul_kronecker_mul M N (1 : Matrix κ κ F2) (1 : Matrix κ κ F2)
    rw [Matrix.mul_one] at this
    exact this
  rw [h]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((inc e)ᵀ) (inc e), inc_t_mul, Matrix.one_mul]

theorem blow_dg (e : μ × κ ↪ ι) (T : Finset μ) :
    blow e (dg T) = dg ((T ×ˢ (univ : Finset κ)).map e) := by
  unfold blow
  rw [← inc_mul_diag]
  congr 2
  ext ⟨a, c⟩ ⟨b, d⟩
  simp only [Matrix.kroneckerMap_apply, dg, Matrix.diagonal_apply, Matrix.one_apply,
    Finset.mem_product, Finset.mem_univ, and_true, Prod.mk.injEq]
  by_cases h1 : a = b <;> by_cases h2 : c = d <;> simp [h1, h2]

/-- The complement of the blow-up of one. -/
def blowC (e : μ × κ ↪ ι) : Matrix ι ι F2 := 1 - blow e 1

theorem blow_mul_blowC (e : μ × κ ↪ ι) (M : Matrix μ μ F2) : blow e M * blowC e = 0 := by
  rw [blowC, Matrix.mul_sub, ← blow_mul, Matrix.mul_one, Matrix.mul_one, sub_self]

theorem blowC_mul_blow (e : μ × κ ↪ ι) (M : Matrix μ μ F2) : blowC e * blow e M = 0 := by
  rw [blowC, Matrix.sub_mul, ← blow_mul, Matrix.one_mul, Matrix.one_mul, sub_self]

theorem blowC_sq (e : μ × κ ↪ ι) : blowC e * blowC e = blowC e := by
  conv_lhs => rw [blowC, Matrix.sub_mul, ← blowC, blow_mul_blowC, Matrix.one_mul, sub_zero]

theorem blow_unit_aux (e : μ × κ ↪ ι) {M N : Matrix μ μ F2} (h : M * N = 1) :
    (blow e M + blowC e) * (blow e N + blowC e) = 1 := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, ← blow_mul, h, blow_mul_blowC,
    blowC_mul_blow, blowC_sq, add_zero, zero_add, blowC]
  abel

/-- Blow-ups of invertible matrices, extended by the identity. -/
def blowU (e : μ × κ ↪ ι) (p : GLM μ) : GLM ι where
  val := blow e p + blowC e
  inv := blow e (p⁻¹ : GLM μ) + blowC e
  val_inv := blow_unit_aux e (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
  inv_val := blow_unit_aux e (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])

theorem blowU_mul (e : μ × κ ↪ ι) (p q : GLM μ) (M : Matrix μ μ F2) :
    (blowU e p : Matrix ι ι F2) * blow e M * (blowU e q : Matrix ι ι F2) =
      blow e ((p : Matrix μ μ F2) * M * (q : Matrix μ μ F2)) := by
  show (blow e p + blowC e) * blow e M * (blow e q + blowC e) = _
  rw [Matrix.add_mul, blowC_mul_blow, add_zero, Matrix.mul_add, ← blow_mul, blow_mul_blowC,
    add_zero, ← blow_mul]

/-- The contraction hypothesis of the contracting case for a function on a group: along every additive map
from μ×μ matrices, full rank is only `s²` times as far as rank one. -/
def Contr {G : Type*} [Group G] (l : Len G) (μ : ℕ) (s : ℝ) : Prop :=
  ∀ τ : Matrix (Fin μ) (Fin μ) F2 → G, (∀ M N, τ (M + N) = τ M * τ N) →
    ∀ i, DM (fun M => l.val (τ M)) (dg univ) ≤ s ^ 2 * DM (fun M => l.val (τ M)) (dg {i})

theorem DM_blow (e : μ × κ ↪ ι) (f : Matrix ι ι F2 → ℝ) (M : Matrix μ μ F2) :
    ∑ p : GLM ι, ∑ q : GLM ι,
      DM (fun N => f ((p : Matrix ι ι F2) * blow e N * (q : Matrix ι ι F2))) M =
      (Fintype.card (GLM μ) : ℝ) ^ 2 * DM f (blow e M) := by
  have h : ∀ a b : GLM μ, ∑ p : GLM ι, ∑ q : GLM ι,
      f ((p : Matrix ι ι F2) * blow e ((a : Matrix μ μ F2) * M * (b : Matrix μ μ F2)) *
        (q : Matrix ι ι F2)) ^ 2 = DM f (blow e M) := by
    intro a b
    rw [← blowU_mul, ← DM_mul f (blowU e a) (blowU e b) (blow e M)]
    rfl
  simp only [DM] at h ⊢
  calc _ = ∑ p : GLM ι, ∑ a : GLM μ, ∑ q : GLM ι, ∑ b : GLM μ,
      f ((p : Matrix ι ι F2) * blow e ((a : Matrix μ μ F2) * M * (b : Matrix μ μ F2)) *
        (q : Matrix ι ι F2)) ^ 2 := sum_congr rfl fun p _ => sum_comm
    _ = ∑ a : GLM μ, ∑ p : GLM ι, ∑ q : GLM ι, ∑ b : GLM μ,
      f ((p : Matrix ι ι F2) * blow e ((a : Matrix μ μ F2) * M * (b : Matrix μ μ F2)) *
        (q : Matrix ι ι F2)) ^ 2 := sum_comm
    _ = ∑ a : GLM μ, ∑ p : GLM ι, ∑ b : GLM μ, ∑ q : GLM ι,
      f ((p : Matrix ι ι F2) * blow e ((a : Matrix μ μ F2) * M * (b : Matrix μ μ F2)) *
        (q : Matrix ι ι F2)) ^ 2 :=
        sum_congr rfl fun a _ => sum_congr rfl fun p _ => sum_comm
    _ = ∑ a : GLM μ, ∑ b : GLM μ, ∑ p : GLM ι, ∑ q : GLM ι,
      f ((p : Matrix ι ι F2) * blow e ((a : Matrix μ μ F2) * M * (b : Matrix μ μ F2)) *
        (q : Matrix ι ι F2)) ^ 2 := sum_congr rfl fun a _ => sum_comm
    _ = _ := by
      rw [sum_congr rfl fun a _ => sum_congr rfl fun b _ => h a b]
      simp only [sum_const, card_univ, nsmul_eq_mul]
      ring

variable {G : Type*} [Group G]

theorem DM_digit (l : Len G) {m : ℕ} {s : ℝ} (hC : Contr l m s)
    (τ : Matrix ι ι F2 → G) (hτ : ∀ M N, τ (M + N) = τ M * τ N) (e : Fin m × κ ↪ ι) (i : Fin m) :
    DM (fun M => l.val (τ M)) (dg ((univ : Finset (Fin m × κ)).map e)) ≤
      s ^ 2 * DM (fun M => l.val (τ M)) (dg ((({i} : Finset (Fin m)) ×ˢ univ).map e)) := by
  have h0 : (0 : ℝ) < (Fintype.card (GLM (Fin m)) : ℝ) ^ 2 := by
    have : 0 < Fintype.card (GLM (Fin m)) := Fintype.card_pos
    positivity
  refine le_of_mul_le_mul_left ?_ h0
  rw [mul_left_comm, ← univ_product_univ, ← blow_dg, ← blow_dg, ← DM_blow, ← DM_blow, mul_sum]
  refine sum_le_sum fun p _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun q _ => ?_
  exact hC (fun N => τ ((p : Matrix ι ι F2) * blow e N * (q : Matrix ι ι F2)))
    (fun M N => by rw [blow_add, Matrix.mul_add, Matrix.add_mul, hτ]) i

end Nc.Flag

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The growth function and what a contracting length gives along a homomorphism from matrices
-/

open Finset Matrix

namespace Nc.Flag

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [Group G]

/-- The growth allowed by the contraction. -/
noncomputable def grow (m : ℕ) (s : ℝ) (r : ℕ) : ℝ :=
  m * (Nat.log m r + 1) * s ^ Nat.log m r

theorem grow_nonneg (m : ℕ) {s : ℝ} (hs : 1 ≤ s) (r : ℕ) : 0 ≤ grow m s r := by
  unfold grow
  positivity

theorem grow_mono (m : ℕ) {s : ℝ} (hs : 1 ≤ s) {r r' : ℕ} (h : r ≤ r') :
    grow m s r ≤ grow m s r' := by
  unfold grow
  have hl : Nat.log m r ≤ Nat.log m r' := Nat.log_mono_right h
  have hl' : (Nat.log m r : ℝ) ≤ Nat.log m r' := by exact_mod_cast hl
  have hp : s ^ Nat.log m r ≤ s ^ Nat.log m r' := pow_le_pow_right₀ hs hl
  have : 0 ≤ s ^ Nat.log m r := by positivity
  gcongr

/-- Facts about `f = l ∘ τ`. -/
structure Good (f : Matrix ι ι F2 → ℝ) (m : ℕ) (s : ℝ) : Prop where
  nonneg : ∀ M, 0 ≤ f M
  zero : f 0 = 0
  add : ∀ M N, f (M + N) ≤ f M + f N
  digit : ∀ (q : ℕ) (e : Fin m × Fin q ↪ ι) (i : Fin m),
    DM f (dg ((univ : Finset (Fin m × Fin q)).map e)) ≤
      s ^ 2 * DM f (dg ((({i} : Finset (Fin m)) ×ˢ univ).map e))

theorem good_of_contr (l : Len G) {m : ℕ} {s : ℝ} (hC : Contr l m s)
    (τ : Matrix ι ι F2 → G) (hτ : ∀ M N, τ (M + N) = τ M * τ N) :
    Good (fun M => l.val (τ M)) m s where
  nonneg _ := l.nonneg _
  zero := by
    have h := hτ 0 0
    rw [add_zero] at h
    have : τ 0 = 1 := by simpa using h
    simp only [this, l.one']
  add M N := by
    simp only [hτ]
    exact l.mul' _ _
  digit _ e i := DM_digit l hC τ hτ e i

variable {f : Matrix ι ι F2 → ℝ} {m : ℕ} {s : ℝ}

theorem Good.dg_zero (h : Good f m s) : DM f (dg (∅ : Finset ι)) = 0 := by
  simp [DM, dg_empty, h.zero]

end Nc.Flag

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The unitriangular group over F₂
-/

namespace Nc.Tower

open Matrix Finset

/-- The entries above the diagonal are free. -/
noncomputable def equivU (h : ℕ) : U h ≃ ({p : Fin h × Fin h // p.1 < p.2} → ZMod 2) where
  toFun A p := A.1.1 p.1.1 p.1.2
  invFun f := ⟨⟨Matrix.of fun i j => if hij : i < j then f ⟨(i, j), hij⟩ else if i = j then 1 else 0, by
      rw [Matrix.det_of_isUpperTriangular]
      · simp
      · intro i j hij
        have hij' : j < i := hij
        simp [not_lt_of_gt hij', hij'.ne']⟩, by
    intro i j
    refine ⟨fun hij => ?_, ?_⟩
    · simp [not_lt_of_gt hij, hij.ne']
    · simp⟩
  left_inv A := by
    refine Subtype.ext (Subtype.ext ?_)
    ext i j
    simp only [Matrix.of_apply]
    split_ifs with h1 h2
    · rfl
    · rw [h2]; exact ((A.2 j j).2).symm
    · exact ((A.2 i j).1 (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2))).symm
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, hij⟩ := p
    have hij' : i < j := hij
    simp [hij']

theorem card_pairs (h : ℕ) : Fintype.card {p : Fin h × Fin h // p.1 < p.2} = h * (h - 1) / 2 := by
  rw [Fintype.card_subtype, ← Finset.univ_product_univ, Finset.card_filter, Finset.sum_product]
  have h1 : ∀ i : Fin h, (∑ j : Fin h, if i < j then 1 else 0) = h - 1 - i.1 := by
    intro i
    rw [← Finset.card_filter]
    have := Fin.card_Ioi i
    rw [← this]
    congr 1
    ext j
    simp
  rw [Finset.sum_congr rfl fun i _ => h1 i, Fin.sum_univ_eq_sum_range (fun i => h - 1 - i),
    Finset.sum_range_reflect (fun i => i) h, Finset.sum_range_id]

/-- The order of U h. -/
theorem card_U (h : ℕ) : Fintype.card (U h) = 2 ^ (h * (h - 1) / 2) := by
  rw [Fintype.card_congr (equivU h), Fintype.card_fun, ZMod.card, card_pairs]

end Nc.Tower

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The unitriangular group: windows, blocks, reflections
-/

open Finset Matrix

namespace Nc.Flag

open Nc.Tower (U SL2 lo hi x)

/-- The matrix of an element. -/
abbrev mat {h : ℕ} (A : U h) : Matrix (Fin h) (Fin h) F2 := A.1.1

theorem mat_inj {h : ℕ} {A B : U h} (hAB : mat A = mat B) : A = B := Subtype.ext (Subtype.ext hAB)

theorem mat_mul {h : ℕ} (A B : U h) : mat (A * B) = mat A * mat B := rfl

theorem mat_one {h : ℕ} : mat (1 : U h) = 1 := rfl

theorem mat_x {h : ℕ} (j : Fin (h - 1)) : mat (x h j) = 1 + Matrix.single (lo j) (hi j) 1 := rfl

theorem mat_lt {h : ℕ} (A : U h) {i j : Fin h} (hij : j < i) : mat A i j = 0 := (A.2 i j).1 hij

theorem mat_diag {h : ℕ} (A : U h) (i : Fin h) : mat A i i = 1 := (A.2 i i).2

/-- An element from its matrix. -/
def mk {h : ℕ} (M : Matrix (Fin h) (Fin h) F2) (h0 : ∀ i j, j < i → M i j = 0)
    (h1 : ∀ i, M i i = 1) : U h :=
  ⟨⟨M, by
    rw [Matrix.det_of_isUpperTriangular]
    · simp [h1]
    · intro i j hij
      exact h0 i j hij⟩, fun i j => ⟨h0 i j, h1 i⟩⟩

theorem mat_mk {h : ℕ} (M : Matrix (Fin h) (Fin h) F2) (h0 : ∀ i j, j < i → M i j = 0)
    (h1 : ∀ i, M i i = 1) : mat (mk M h0 h1) = M := rfl

section Win
variable {p n h : ℕ} (hp : p + n ≤ h)

/-- The place of an index of a window. -/
def we (i : Fin n) : Fin h := ⟨p + i.1, by omega⟩

theorem we_inj {i j : Fin n} : we hp i = we hp j ↔ i = j := by
  simp only [we, Fin.ext_iff]
  omega

theorem we_lt {i j : Fin n} : we hp i < we hp j ↔ i < j := by
  simp only [we, Fin.lt_def]
  omega

/-- The inclusion matrix of a window. -/
def wi : Matrix (Fin h) (Fin n) F2 := Matrix.of fun i a => if i = we hp a then 1 else 0

theorem wi_t_mul : (wi hp)ᵀ * wi hp = 1 := by
  ext a b
  simp [Matrix.mul_apply, wi, Matrix.one_apply, we_inj, eq_comm]

theorem wi_mul_apply (A : Matrix (Fin n) (Fin n) F2) (i j : Fin h) :
    (wi hp * A * (wi hp)ᵀ) i j =
      ∑ b, ∑ a, if i = we hp a ∧ j = we hp b then A a b else 0 := by
  simp only [Matrix.mul_apply, wi, Matrix.of_apply, Matrix.transpose_apply, sum_mul]
  refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
  by_cases h1 : i = we hp a <;> by_cases h2 : j = we hp b <;> simp [h1, h2]

theorem wi_mul_we (A : Matrix (Fin n) (Fin n) F2) (a b : Fin n) :
    (wi hp * A * (wi hp)ᵀ) (we hp a) (we hp b) = A a b := by
  rw [wi_mul_apply, sum_eq_single b, sum_eq_single a]
  · simp
  · intro c _ hc
    simp [we_inj, hc.symm]
  · simp
  · intro c _ hc
    simp [we_inj, hc.symm]
  · simp

theorem wi_mul_not (A : Matrix (Fin n) (Fin n) F2) {i : Fin h} (hi : ∀ a, i ≠ we hp a)
    (j : Fin h) : (wi hp * A * (wi hp)ᵀ) i j = 0 := by
  rw [wi_mul_apply]
  simp [hi]

theorem wi_mul_not' (A : Matrix (Fin n) (Fin n) F2) {j : Fin h} (hj : ∀ a, j ≠ we hp a)
    (i : Fin h) : (wi hp * A * (wi hp)ᵀ) i j = 0 := by
  rw [wi_mul_apply]
  simp [hj]

/-- The matrix of a window element. -/
def wm (A : Matrix (Fin n) (Fin n) F2) : Matrix (Fin h) (Fin h) F2 :=
  wi hp * A * (wi hp)ᵀ + (1 - wi hp * (1 : Matrix (Fin n) (Fin n) F2) * (wi hp)ᵀ)

theorem wm_one : wm hp 1 = 1 := by
  simp [wm]

theorem wm_mul (A B : Matrix (Fin n) (Fin n) F2) : wm hp (A * B) = wm hp A * wm hp B := by
  have hmul : ∀ C D : Matrix (Fin n) (Fin n) F2,
      (wi hp * C * (wi hp)ᵀ) * (wi hp * D * (wi hp)ᵀ) = wi hp * (C * D) * (wi hp)ᵀ := by
    intro C D
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((wi hp)ᵀ) (wi hp), wi_t_mul, Matrix.one_mul]
  unfold wm
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, hmul]
  simp only [Matrix.mul_one, Matrix.one_mul]
  abel

/-- The embedding of the unitriangular group of a window. -/
def win : U n →* U h where
  toFun A := mk (wm hp (mat A))
    (by
      intro i j hij
      unfold wm
      rw [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply_ne hij.ne']
      by_cases h1 : ∃ a, i = we hp a
      · obtain ⟨a, rfl⟩ := h1
        by_cases h2 : ∃ b, j = we hp b
        · obtain ⟨b, rfl⟩ := h2
          have hba : b < a := (we_lt hp).1 hij
          rw [wi_mul_we, wi_mul_we, mat_lt A hba, Matrix.one_apply_ne hba.ne']
          simp
        · push_neg at h2
          rw [wi_mul_not' hp _ h2, wi_mul_not' hp _ h2]
          simp
      · push_neg at h1
        rw [wi_mul_not hp _ h1, wi_mul_not hp _ h1]
        simp)
    (by
      intro i
      unfold wm
      rw [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply_eq]
      by_cases h1 : ∃ a, i = we hp a
      · obtain ⟨a, rfl⟩ := h1
        rw [wi_mul_we, wi_mul_we, mat_diag, Matrix.one_apply_eq]
        simp
      · push_neg at h1
        rw [wi_mul_not hp _ h1, wi_mul_not hp _ h1]
        simp)
  map_one' := mat_inj (by rw [mat_mk, mat_one, wm_one, mat_one])
  map_mul' A B := mat_inj (by rw [mat_mk, mat_mul, wm_mul]; rfl)

theorem mat_win (A : U n) : mat (win hp A) = wm hp (mat A) := rfl

/-- The place of a type of a window. -/
def wt (j : Fin (n - 1)) : Fin (h - 1) := ⟨p + j.1, by omega⟩

theorem win_x (j : Fin (n - 1)) : win hp (x n j) = x h (wt hp j) := by
  apply mat_inj
  rw [mat_win, mat_x, mat_x, wm, Matrix.mul_add, Matrix.add_mul]
  have : wi hp * Matrix.single (lo j) (hi j) (1 : F2) * (wi hp)ᵀ =
      Matrix.single (lo (wt hp j)) (hi (wt hp j)) (1 : F2) := by
    ext a b
    rw [wi_mul_apply, Matrix.single_apply, sum_eq_single (hi j), sum_eq_single (lo j)]
    · have h1 : we hp (lo j) = lo (wt hp j) := rfl
      have h2 : we hp (hi j) = hi (wt hp j) := rfl
      rw [h1, h2, Matrix.single_apply_same]
      simp only [eq_comm]
    · intro c _ hc
      rw [Matrix.single_apply_of_ne]
      · simp
      · exact fun h => hc h.1.symm
    · simp
    · intro c _ hc
      refine sum_eq_zero fun d _ => ?_
      rw [Matrix.single_apply_of_ne]
      · simp
      · exact fun h => hc h.2.symm
    · simp
  rw [this]
  abel

end Win

section Blocks
variable {a b : ℕ}

theorem hl : 0 + a ≤ a + b := by omega
theorem hr : a + b ≤ a + b := le_rfl

theorem wi_lr : (wi (hl (a := a) (b := b)))ᵀ * wi (hr (a := a) (b := b)) = 0 := by
  ext i j
  simp only [Matrix.mul_apply, wi, Matrix.of_apply, Matrix.transpose_apply, Matrix.zero_apply]
  refine sum_eq_zero fun k _ => ?_
  by_cases h1 : k = we (hl (a := a) (b := b)) i
  · have h2 : k ≠ we (hr (a := a) (b := b)) j := by
      rw [h1]
      simp only [we, ne_eq, Fin.ext_iff]
      omega
    simp [h2]
  · simp [h1]

theorem wi_rl : (wi (hr (a := a) (b := b)))ᵀ * wi (hl (a := a) (b := b)) = 0 := by
  rw [← Matrix.transpose_transpose (wi (hl (a := a) (b := b))), ← Matrix.transpose_mul, wi_lr,
    Matrix.transpose_zero]

theorem wi_add : wi (hl (a := a) (b := b)) * (wi (hl (a := a) (b := b)))ᵀ +
    wi (hr (a := a) (b := b)) * (wi (hr (a := a) (b := b)))ᵀ = 1 := by
  ext i j
  have h1 := wi_mul_apply (hl (a := a) (b := b)) 1 i j
  have h2 := wi_mul_apply (hr (a := a) (b := b)) 1 i j
  rw [Matrix.mul_one] at h1 h2
  rw [Matrix.add_apply, h1, h2]
  clear h1 h2
  by_cases hi : i.1 < a
  · obtain ⟨k, rfl⟩ : ∃ k, i = we (hl (a := a) (b := b)) k := ⟨⟨i.1, hi⟩, by simp [we]⟩
    have h3 : ∀ c, we (hl (a := a) (b := b)) k ≠ we (hr (a := a) (b := b)) c := by
      intro c
      simp only [we, ne_eq, Fin.ext_iff]
      omega
    simp only [h3, false_and, if_false, sum_const_zero, add_zero, we_inj, Matrix.one_apply]
    rw [sum_congr rfl fun b _ => sum_eq_single k (by
      intro c _ hc
      simp [hc.symm]) (by simp)]
    simp only [true_and]
    by_cases hj : ∃ l, j = we (hl (a := a) (b := b)) l
    · obtain ⟨l, rfl⟩ := hj
      rw [sum_eq_single l]
      · simp [we_inj]
      · intro c _ hc
        simp [we_inj, hc.symm]
      · simp
    · push_neg at hj
      simp [hj, (hj k).symm]
  · obtain ⟨k, rfl⟩ : ∃ k, i = we (hr (a := a) (b := b)) k :=
      ⟨⟨i.1 - a, by omega⟩, by simp only [we, Fin.ext_iff]; omega⟩
    have h3 : ∀ c, we (hr (a := a) (b := b)) k ≠ we (hl (a := a) (b := b)) c := by
      intro c
      simp only [we, ne_eq, Fin.ext_iff]
      omega
    simp only [h3, false_and, if_false, sum_const_zero, zero_add, we_inj, Matrix.one_apply]
    rw [sum_congr rfl fun b _ => sum_eq_single k (by
      intro c _ hc
      simp [hc.symm]) (by simp)]
    simp only [true_and]
    by_cases hj : ∃ l, j = we (hr (a := a) (b := b)) l
    · obtain ⟨l, rfl⟩ := hj
      rw [sum_eq_single l]
      · simp [we_inj]
      · intro c _ hc
        simp [we_inj, hc.symm]
      · simp
    · push_neg at hj
      simp [hj, (hj k).symm]

end Blocks

end Nc.Flag

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The block decomposition of the unitriangular group
-/

open Finset Matrix

namespace Nc.Flag

open Nc.Tower (U SL2 lo hi x)

variable {a b : ℕ}

/-- The inclusion of the first window. -/
abbrev wl (a b : ℕ) : Matrix (Fin (a + b)) (Fin a) F2 := wi (hl (a := a) (b := b))

/-- The inclusion of the second window. -/
abbrev wr (a b : ℕ) : Matrix (Fin (a + b)) (Fin b) F2 := wi (hr (a := a) (b := b))

/-- The elements `1 + M` with `M` in the upper right block. -/
def up (M : Matrix (Fin a) (Fin b) F2) : U (a + b) :=
  mk (1 + wl a b * M * (wr a b)ᵀ)
    (by
      intro i j hij
      rw [Matrix.add_apply, Matrix.one_apply_ne hij.ne', zero_add, Matrix.mul_apply]
      refine sum_eq_zero fun k _ => ?_
      rw [Matrix.mul_apply, sum_mul]
      refine sum_eq_zero fun l _ => ?_
      simp only [wi, Matrix.of_apply, Matrix.transpose_apply]
      by_cases h1 : i = we (hl (a := a) (b := b)) l
      · by_cases h2 : j = we (hr (a := a) (b := b)) k
        · exfalso
          rw [h1, h2] at hij
          simp only [we, Fin.lt_def] at hij
          omega
        · simp [h2]
      · simp [h1])
    (by
      intro i
      rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply]
      rw [sum_eq_zero, add_zero]
      intro k _
      rw [Matrix.mul_apply, sum_mul]
      refine sum_eq_zero fun l _ => ?_
      simp only [wi, Matrix.of_apply, Matrix.transpose_apply]
      by_cases h1 : i = we (hl (a := a) (b := b)) l
      · by_cases h2 : i = we (hr (a := a) (b := b)) k
        · exfalso
          rw [h1] at h2
          simp only [we, Fin.ext_iff] at h2
          omega
        · simp [h2]
      · simp [h1])

theorem mat_up (M : Matrix (Fin a) (Fin b) F2) : mat (up M) = 1 + wl a b * M * (wr a b)ᵀ := rfl

theorem up_add (M N : Matrix (Fin a) (Fin b) F2) : up (M + N) = up M * up N := by
  apply mat_inj
  rw [mat_mul, mat_up, mat_up, mat_up]
  have : wl a b * M * (wr a b)ᵀ * (wl a b * N * (wr a b)ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((wr a b)ᵀ) (wl a b), wi_rl]
    simp
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, this]
  abel

theorem wm_l (A : Matrix (Fin a) (Fin a) F2) : wm (hl (a := a) (b := b)) A =
    wl a b * A * (wl a b)ᵀ + wr a b * (wr a b)ᵀ := by
  rw [wm, Matrix.mul_one, ← wi_add (a := a) (b := b)]
  abel

theorem wm_r (A : Matrix (Fin b) (Fin b) F2) : wm (hr (a := a) (b := b)) A =
    wr a b * A * (wr a b)ᵀ + wl a b * (wl a b)ᵀ := by
  rw [wm, Matrix.mul_one, ← wi_add (a := a) (b := b)]
  abel

/-- The element with given blocks. -/
def blk (t : U a × Matrix (Fin a) (Fin b) F2 × U b) : U (a + b) :=
  win (hr (a := a) (b := b)) t.2.2 * up t.2.1 * win (hl (a := a) (b := b)) t.1

theorem mat_blk (t : U a × Matrix (Fin a) (Fin b) F2 × U b) : mat (blk t) =
    wl a b * mat t.1 * (wl a b)ᵀ + wl a b * t.2.1 * (wr a b)ᵀ + wr a b * mat t.2.2 * (wr a b)ᵀ := by
  obtain ⟨A, M, C⟩ := t
  have z1 : ∀ {c d : ℕ} (P : Matrix (Fin (a + b)) (Fin c) F2) (Q : Matrix (Fin d) (Fin (a + b)) F2)
      (X : Matrix (Fin c) (Fin a) F2) (Y : Matrix (Fin b) (Fin d) F2),
      P * X * (wl a b)ᵀ * (wr a b * Y * Q) = 0 := by
    intro c d P Q X Y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((wl a b)ᵀ) (wr a b), wi_lr]
    simp
  have z2 : ∀ {c d : ℕ} (P : Matrix (Fin (a + b)) (Fin c) F2) (Q : Matrix (Fin d) (Fin (a + b)) F2)
      (X : Matrix (Fin c) (Fin b) F2) (Y : Matrix (Fin a) (Fin d) F2),
      P * X * (wr a b)ᵀ * (wl a b * Y * Q) = 0 := by
    intro c d P Q X Y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((wr a b)ᵀ) (wl a b), wi_rl]
    simp
  have e1 : ∀ {c d : ℕ} (P : Matrix (Fin (a + b)) (Fin c) F2) (Q : Matrix (Fin d) (Fin (a + b)) F2)
      (X : Matrix (Fin c) (Fin a) F2) (Y : Matrix (Fin a) (Fin d) F2),
      P * X * (wl a b)ᵀ * (wl a b * Y * Q) = P * (X * Y) * Q := by
    intro c d P Q X Y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((wl a b)ᵀ) (wl a b), wi_t_mul, Matrix.one_mul]
  have e2 : ∀ {c d : ℕ} (P : Matrix (Fin (a + b)) (Fin c) F2) (Q : Matrix (Fin d) (Fin (a + b)) F2)
      (X : Matrix (Fin c) (Fin b) F2) (Y : Matrix (Fin b) (Fin d) F2),
      P * X * (wr a b)ᵀ * (wr a b * Y * Q) = P * (X * Y) * Q := by
    intro c d P Q X Y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((wr a b)ᵀ) (wr a b), wi_t_mul, Matrix.one_mul]
  have s1 : wl a b * (wl a b)ᵀ = wl a b * (1 : Matrix (Fin a) (Fin a) F2) * (wl a b)ᵀ := by
    rw [Matrix.mul_one]
  have s2 : wr a b * (wr a b)ᵀ = wr a b * (1 : Matrix (Fin b) (Fin b) F2) * (wr a b)ᵀ := by
    rw [Matrix.mul_one]
  show mat (win (hr (a := a) (b := b)) C * up M * win (hl (a := a) (b := b)) A) = _
  rw [mat_mul, mat_mul, mat_win, mat_win, mat_up, wm_l, wm_r, ← wi_add (a := a) (b := b), s1, s2]
  simp only [Matrix.add_mul, Matrix.mul_add, z1, z2, e1, e2, add_zero, zero_add]
  simp only [Matrix.mul_one, Matrix.one_mul]
  abel

theorem blk_injective : Function.Injective (blk : U a × Matrix (Fin a) (Fin b) F2 × U b → U (a + b)) := by
  intro s t hst
  have h := congrArg mat hst
  rw [mat_blk, mat_blk] at h
  have k1 : ∀ t : U a × Matrix (Fin a) (Fin b) F2 × U b,
      (wl a b)ᵀ * (wl a b * mat t.1 * (wl a b)ᵀ + wl a b * t.2.1 * (wr a b)ᵀ +
        wr a b * mat t.2.2 * (wr a b)ᵀ) * wl a b = mat t.1 := by
    intro t
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, wi_t_mul, wi_rl, Matrix.mul_zero,
      Matrix.mul_one, add_zero]
    rw [← Matrix.mul_assoc, wi_t_mul, Matrix.one_mul]
  have k2 : ∀ t : U a × Matrix (Fin a) (Fin b) F2 × U b,
      (wl a b)ᵀ * (wl a b * mat t.1 * (wl a b)ᵀ + wl a b * t.2.1 * (wr a b)ᵀ +
        wr a b * mat t.2.2 * (wr a b)ᵀ) * wr a b = t.2.1 := by
    intro t
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, wi_t_mul, wi_lr, Matrix.mul_zero,
      Matrix.mul_one, zero_add]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, wi_t_mul, wi_lr, Matrix.one_mul, Matrix.zero_mul,
      add_zero]
  have k3 : ∀ t : U a × Matrix (Fin a) (Fin b) F2 × U b,
      (wr a b)ᵀ * (wl a b * mat t.1 * (wl a b)ᵀ + wl a b * t.2.1 * (wr a b)ᵀ +
        wr a b * mat t.2.2 * (wr a b)ᵀ) * wr a b = mat t.2.2 := by
    intro t
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, wi_t_mul, wi_lr, Matrix.mul_zero,
      Matrix.mul_one, zero_add]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, wi_t_mul, wi_rl, Matrix.one_mul, Matrix.zero_mul,
      zero_add]
  refine Prod.ext (mat_inj ?_) (Prod.ext ?_ (mat_inj ?_))
  · rw [← k1 s, ← k1 t, h]
  · rw [← k2 s, ← k2 t, h]
  · rw [← k3 s, ← k3 t, h]

theorem two_mul_tri (n : ℕ) : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd

theorem tri_add (a b : ℕ) : (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + a * b + b * (b - 1) / 2 := by
  have h1 := two_mul_tri a
  have h2 := two_mul_tri b
  have h3 := two_mul_tri (a + b)
  have h4 : (a + b) * (a + b - 1) = a * (a - 1) + 2 * (a * b) + b * (b - 1) := by
    rcases a with - | a
    · simp
    · rcases b with - | b
      · simp
      · simp only [Nat.add_sub_cancel, show a + 1 + (b + 1) - 1 = a + b + 1 by omega]
        ring
  omega

theorem blk_bijective : Function.Bijective (blk : U a × Matrix (Fin a) (Fin b) F2 × U b → U (a + b)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨blk_injective, ?_⟩
  have hM : Fintype.card (Matrix (Fin a) (Fin b) F2) = 2 ^ (a * b) := by
    rw [show Fintype.card (Matrix (Fin a) (Fin b) F2) = Fintype.card (Fin a → Fin b → F2) from rfl]
    simp [← pow_mul, mul_comm]
  rw [Fintype.card_prod, Fintype.card_prod, hM, Nc.Tower.card_U, Nc.Tower.card_U, Nc.Tower.card_U,
    tri_add, pow_add, pow_add]
  ring

end Nc.Flag

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Elements `1 + uφᵀ` of the unitriangular group are short words
-/

open Finset Matrix

namespace Nc.Flag

open Nc.Tower (U SL2 lo hi x)

variable {n : ℕ}

/-- The total length of the generators. -/
noncomputable def Len.S (l : Len (U n)) : ℝ := ∑ j : Fin (n - 1), l.val (x n j)

theorem Len.S_nonneg (l : Len (U n)) : 0 ≤ l.S := sum_nonneg fun _ _ => l.nonneg _

theorem Len.x_le_S (l : Len (U n)) (j : Fin (n - 1)) : l.val (x n j) ≤ l.S :=
  single_le_sum (f := fun j => l.val (x n j)) (fun _ _ => l.nonneg _) (mem_univ j)

theorem x_mul_apply (j : Fin (n - 1)) (A : U n) (i k : Fin n) :
    mat (x n j * A) i k = mat A i k + if i = lo j then mat A (hi j) k else 0 := by
  rw [mat_mul, mat_x, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
  congr 1
  by_cases h : i = lo j
  · subst h
    simp
  · rw [if_neg h]
    simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm h]

theorem mul_x_apply (j : Fin (n - 1)) (A : U n) (i k : Fin n) :
    mat (A * x n j) i k = mat A i k + if k = hi j then mat A i (lo j) else 0 := by
  rw [mat_mul, mat_x, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases h : k = hi j
  · subst h
    simp
  · rw [if_neg h]
    simp [Matrix.mul_apply, Matrix.single_apply, Ne.symm h]

theorem f2_add_self (a : F2) : a + a = 0 := CharTwo.add_self_eq_zero a

theorem lo_ne_hi' (j : Fin (n - 1)) : hi j ≠ lo j := (Nc.Tower.lo_ne_hi j).symm

theorem x_mul_x (j : Fin (n - 1)) : x n j * x n j = 1 := by
  apply mat_inj
  ext i k
  rw [x_mul_apply, mat_x, mat_one]
  by_cases h : i = lo j
  · subst h
    simp only [Matrix.add_apply, if_true, Matrix.single_apply]
    by_cases h2 : hi j = k
    · subst h2
      simp [lo_ne_hi', f2_add_self, (lo_ne_hi' j).symm]
    · simp [h2, (lo_ne_hi' j).symm, Matrix.one_apply]
  · simp [h, Matrix.single_apply, Ne.symm h]

/-- The sum of the lengths of the generators of types ≥ p. -/
noncomputable def Len.T (l : Len (U n)) (p : ℕ) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin (n - 1) => p ≤ j.1), l.val (x n j)

theorem Len.T_zero (l : Len (U n)) : l.T 0 = l.S := by
  simp [Len.T, Len.S]

theorem Len.T_succ (l : Len (U n)) (j : Fin (n - 1)) : l.T j.1 = l.T (j.1 + 1) + l.val (x n j) := by
  unfold Len.T
  have : univ.filter (fun i : Fin (n - 1) => j.1 ≤ i.1) =
      insert j (univ.filter fun i : Fin (n - 1) => j.1 + 1 ≤ i.1) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  rw [this, sum_insert (by simp), add_comm]

theorem exists_col_aux (l : Len (U n)) (a : Fin n) (k : ℕ) : ∀ p : ℕ, p + k = a.1 →
    ∀ u : Fin n → F2, u a = 1 → (∀ i, a < i → u i = 0) → (∀ i : Fin n, i.1 < p → u i = 0) →
    ∃ c d : U n, (∀ i j : Fin n, (i.1 < p ∨ a ≤ i) → mat c i j = (1 : Matrix _ _ F2) i j) ∧
      (∀ i j : Fin n, (i.1 < p ∨ a ≤ i) → mat d i j = (1 : Matrix _ _ F2) i j) ∧
      (∀ i : Fin n, mat d i a = if p ≤ i.1 ∧ i ≤ a then 1 else 0) ∧
      (∀ i, mat (c * d) i a = u i) ∧ l.val c ≤ l.T p ∧ l.val d ≤ l.T p := by
  induction k with
  | zero =>
    intro p hp u hua hu1 hu2
    have hT : 0 ≤ l.T p := sum_nonneg fun _ _ => l.nonneg _
    refine ⟨1, 1, fun _ _ _ => rfl, fun _ _ _ => rfl, fun i => ?_, fun i => ?_, ?_, ?_⟩
    · rw [mat_one, Matrix.one_apply]
      by_cases h : i = a
      · subst h
        simp; omega
      · rw [if_neg h, if_neg]
        rintro ⟨h1, h2⟩
        exact h (le_antisymm h2 (Fin.le_def.2 (by omega)))
    · rw [mul_one, mat_one, Matrix.one_apply]
      rcases lt_trichotomy i a with h | h | h
      · rw [if_neg h.ne, hu2 i (by rw [Fin.lt_def] at h; omega)]
      · subst h
        rw [if_pos rfl, hua]
      · rw [if_neg h.ne', hu1 i h]
    · rw [l.one']; exact hT
    · rw [l.one']; exact hT
  | succ k ih =>
    intro p hp u hua hu1 hu2
    have hpa : p < a.1 := by omega
    have hpn : p < n - 1 := by have := a.2; omega
    set j : Fin (n - 1) := ⟨p, hpn⟩ with hj
    have hlo : (lo j).1 = p := rfl
    have hhi : (hi j).1 = p + 1 := rfl
    have hloa : lo j ≠ a := by
      intro h
      rw [← h, hlo] at hpa
      omega
    obtain ⟨c, d, hc, hd, hda, hcd, hlc, hld⟩ := ih (p + 1) (by omega)
      (Function.update u (lo j) 0) (by rw [Function.update_of_ne hloa.symm, hua])
      (fun i hi => by
        rw [Function.update_of_ne, hu1 i hi]
        rintro rfl
        rw [Fin.lt_def, hlo] at hi
        omega)
      (fun i hi => by
        by_cases h : i = lo j
        · rw [h, Function.update_self]
        · rw [Function.update_of_ne h]
          apply hu2
          have : i.1 ≠ p := fun h2 => h (Fin.ext h2)
          omega)
    have hT : l.T p = l.T (p + 1) + l.val (x n j) := l.T_succ j
    have hx0 := l.nonneg (x n j)
    have hclo : ∀ i, mat c i (lo j) = (1 : Matrix _ _ F2) i (lo j) := by
      intro i
      by_cases hi : i.1 < p + 1
      · exact hc i _ (Or.inl hi)
      · have h1 : lo j < i := by rw [Fin.lt_def, hlo]; omega
        rw [mat_lt c h1, Matrix.one_apply_ne h1.ne']
    have hrow : ∀ i : Fin n, (i.1 < p ∨ a ≤ i) → i ≠ lo j := by
      rintro i hi rfl
      rw [Fin.le_def, hlo] at hi
      omega
    have hrow' : ∀ i : Fin n, (i.1 < p ∨ a ≤ i) → (i.1 < p + 1 ∨ a ≤ i) := by
      rintro i (h | h)
      · left; omega
      · right; exact h
    have hd' : ∀ i k : Fin n, (i.1 < p ∨ a ≤ i) → mat (x n j * d) i k = (1 : Matrix _ _ F2) i k := by
      intro i k hi
      rw [x_mul_apply, if_neg (hrow i hi), add_zero, hd i k (hrow' i hi)]
    have hda' : ∀ i : Fin n, mat (x n j * d) i a = if p ≤ i.1 ∧ i ≤ a then 1 else 0 := by
      intro i
      rw [x_mul_apply, hda, hda]
      by_cases h : i = lo j
      · subst h
        rw [if_neg (by rw [hlo]; omega), if_pos rfl, if_pos, if_pos, zero_add]
        · exact ⟨hlo.ge, Fin.le_def.2 (by omega)⟩
        · exact ⟨hhi.ge, Fin.le_def.2 (by omega)⟩
      · rw [if_neg h, add_zero]
        have : i.1 ≠ p := fun h2 => h (Fin.ext h2)
        congr 1
        apply propext
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    have hld' : l.val (x n j * d) ≤ l.T p := by
      have := l.mul' (x n j) d
      linarith
    by_cases hu : u (lo j) = 0
    · refine ⟨c * x n j, x n j * d, fun i k hi => ?_, hd', hda', fun i => ?_, ?_, hld'⟩
      · rw [mul_x_apply, hclo, Matrix.one_apply_ne (hrow i hi), ite_self, add_zero,
          hc i k (hrow' i hi)]
      · rw [mul_assoc, ← mul_assoc (x n j), x_mul_x, one_mul, hcd]
        by_cases h : i = lo j
        · rw [h, Function.update_self, hu]
        · rw [Function.update_of_ne h]
      · have := l.mul' c (x n j)
        linarith
    · have hu' : u (lo j) = 1 := by
        have : ∀ a : F2, a ≠ 0 → a = 1 := by decide
        exact this _ hu
      refine ⟨c, x n j * d, fun i k hi => hc i k (hrow' i hi), hd', hda', fun i => ?_, ?_, hld'⟩
      · have e : mat (c * (x n j * d)) i a = mat (c * d) i a + mat c i (lo j) * mat d (hi j) a := by
          rw [mat_mul c (x n j * d), mat_mul c d, Matrix.mul_apply, Matrix.mul_apply]
          simp only [x_mul_apply, mul_add, sum_add_distrib]
          simp
        rw [e, hcd, hclo, hda, if_pos ⟨hhi.ge, Fin.le_def.2 (by omega)⟩, mul_one]
        by_cases h : i = lo j
        · rw [h, Function.update_self, hu', Matrix.one_apply_eq, zero_add]
        · rw [Function.update_of_ne h, Matrix.one_apply_ne h, add_zero]
      · linarith

theorem exists_col (l : Len (U n)) (a : Fin n) (u : Fin n → F2) (hua : u a = 1)
    (hu : ∀ i, a < i → u i = 0) :
    ∃ g : U n, (∀ i j : Fin n, a ≤ i → mat g i j = (1 : Matrix _ _ F2) i j) ∧
      (∀ i, mat g i a = u i) ∧ l.val g ≤ 2 * l.S := by
  obtain ⟨c, d, hc, hd, -, hcd, hlc, hld⟩ := exists_col_aux l a a.1 0 (by omega) u hua hu
    (fun i hi => absurd hi (by omega))
  refine ⟨c * d, fun i j hi => ?_, hcd, ?_⟩
  · rw [mat_mul, Matrix.mul_apply]
    simp only [hc i _ (Or.inr hi)]
    rw [← hd i j (Or.inr hi), ← Matrix.mul_apply, Matrix.one_mul]
  · rw [Len.T_zero] at hlc hld
    have := l.mul' c d
    linarith

/-- Reflection in the antidiagonal. -/
def refl (A : U n) : U n :=
  mk (Matrix.of fun i j => mat A (Fin.rev j) (Fin.rev i))
    (fun i j hij => mat_lt A (Fin.rev_lt_rev.2 hij)) (fun i => mat_diag A _)

theorem refl_apply (A : U n) (i j : Fin n) : mat (refl A) i j = mat A (Fin.rev j) (Fin.rev i) := rfl

theorem refl_mul (A B : U n) : refl (A * B) = refl B * refl A := by
  apply mat_inj
  ext i j
  rw [refl_apply, mat_mul, mat_mul, Matrix.mul_apply, Matrix.mul_apply, ← Equiv.sum_comp Fin.revPerm]
  refine sum_congr rfl fun k _ => ?_
  rw [refl_apply, refl_apply, mul_comm]
  rfl

theorem refl_one : refl (1 : U n) = 1 := by
  apply mat_inj
  ext i j
  rw [refl_apply, mat_one, Matrix.one_apply, Matrix.one_apply]
  simp [Fin.rev_inj, eq_comm]

theorem refl_inv (A : U n) : refl A⁻¹ = (refl A)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← refl_mul, mul_inv_cancel, refl_one]

theorem refl_x (j : Fin (n - 1)) : refl (x n j) = x n (Fin.rev j) := by
  apply mat_inj
  ext i k
  rw [refl_apply, mat_x, mat_x, Matrix.add_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.one_apply, Matrix.single_apply, Matrix.single_apply]
  have h1 : lo j = Fin.rev k ↔ hi (Fin.rev j) = k := by
    simp only [lo, hi, Fin.ext_iff, Fin.val_rev]
    have := j.2; have := k.2
    omega
  have h2 : hi j = Fin.rev i ↔ lo (Fin.rev j) = i := by
    simp only [lo, hi, Fin.ext_iff, Fin.val_rev]
    have := j.2; have := i.2
    omega
  simp only [Fin.rev_inj, h1, h2, eq_comm (a := k), and_comm]

/-- The reflected length. -/
def Len.refl (l : Len (U n)) : Len (U n) where
  val A := l.val (Nc.Flag.refl A)
  one' := by rw [refl_one, l.one']
  inv' g := by rw [refl_inv, l.inv']
  mul' g h := by
    rw [refl_mul, add_comm]
    exact l.mul' _ _

theorem Len.refl_S (l : Len (U n)) : l.refl.S = l.S := by
  unfold Len.S
  rw [← Equiv.sum_comp Fin.revPerm]
  refine sum_congr rfl fun j _ => ?_
  show l.val (Nc.Flag.refl _) = _
  rw [refl_x]
  simp

theorem exists_row (l : Len (U n)) (b : Fin n) (φ : Fin n → F2) (hb : φ b = 1)
    (hφ : ∀ i, i < b → φ i = 0) :
    ∃ g : U n, (∀ i j : Fin n, j ≤ b → mat g i j = (1 : Matrix _ _ F2) i j) ∧
      (∀ j, mat g b j = φ j) ∧ l.val g ≤ 2 * l.S := by
  obtain ⟨g, h1, h2, h3⟩ := exists_col l.refl (Fin.rev b) (fun i => φ (Fin.rev i))
    (by simpa using hb) (fun i hi => hφ _ (by rw [← Fin.rev_lt_rev, Fin.rev_rev]; exact hi))
  refine ⟨refl g, fun i j hj => ?_, fun j => ?_, ?_⟩
  · rw [refl_apply, h1 _ _ (Fin.rev_le_rev.2 hj), Matrix.one_apply, Matrix.one_apply]
    simp [Fin.rev_inj, eq_comm]
  · rw [refl_apply, h2]
    simp
  · rw [Len.refl_S] at h3
    exact h3

theorem lead_le (l : Len (U n)) (j : Fin (n - 1)) (u φ : Fin n → F2) (hu1 : u (lo j) = 1)
    (hu : ∀ i, lo j < i → u i = 0) (hφ1 : φ (hi j) = 1) (hφ : ∀ i, i < hi j → φ i = 0)
    (A : U n) (hA : mat A = 1 + Matrix.vecMulVec u φ) : l.val A ≤ 9 * l.S := by
  obtain ⟨g, hg1, hg2, hg3⟩ := exists_col l (lo j) u hu1 hu
  obtain ⟨k, hk1, hk2, hk3⟩ := exists_row l (hi j) φ hφ1 hφ
  set Y : U n := k⁻¹ * x n j * k with hY
  have hlt := Nc.Tower.lo_lt_hi j
  have hkY : mat (k * Y) = mat k * (1 + Matrix.vecMulVec (Pi.single (lo j) 1) φ) := by
    have : k * Y = x n j * k := by rw [hY]; group
    rw [this]
    ext i m
    rw [x_mul_apply, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, hk2, Matrix.mul_apply]
    congr 1
    simp only [Matrix.vecMulVec_apply]
    rw [sum_eq_single (lo j)]
    · rw [hk1 _ _ hlt.le, Matrix.one_apply, Pi.single_eq_same, one_mul]
      split_ifs <;> simp
    · intro c _ hc
      rw [Pi.single_eq_of_ne hc]
      simp
    · simp
  have hYm : mat Y = 1 + Matrix.vecMulVec (Pi.single (lo j) 1) φ := by
    have h1 : mat k⁻¹ * mat k = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
    rw [mat_mul] at hkY
    calc mat Y = mat k⁻¹ * mat k * mat Y := by rw [h1, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, hkY, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hAg : A * g = g * Y := by
    apply mat_inj
    rw [mat_mul, mat_mul, hA, hYm, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    congr 1
    ext i m
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.vecMulVec_apply]
    have h1 : ∀ c, u i * φ c * mat g c m = u i * φ c * (1 : Matrix (Fin n) (Fin n) F2) c m := by
      intro c
      by_cases hc : c < hi j
      · rw [hφ c hc]; simp
      · rw [hg1 c m (hlt.le.trans (not_lt.1 hc))]
    rw [sum_congr rfl fun c _ => h1 c, sum_eq_single m, sum_eq_single (lo j)]
    · rw [hg2, Pi.single_eq_same, Matrix.one_apply_eq]
      ring
    · intro c _ hc
      rw [Pi.single_eq_of_ne hc]
      simp
    · simp
    · intro c _ hc
      rw [Matrix.one_apply_ne hc, mul_zero]
    · simp
  have hA2 : A = g * Y * g⁻¹ := by rw [← hAg]; group
  have h1 := l.conj g Y
  rw [← hA2] at h1
  have h2 := l.conj k⁻¹ (x n j)
  rw [inv_inv, ← hY, l.inv'] at h2
  have h3 := l.x_le_S j
  linarith

end Nc.Flag

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Lengths on U n: quotients and the two diagonal blocks
-/

open Finset Matrix

namespace Nc.Flag

open Nc.Tower (U SL2 lo hi x)

theorem three_le {T : Type*} [Fintype T] (c f g k : T → ℝ) (hc : ∀ t, 0 ≤ c t) (hf : ∀ t, 0 ≤ f t)
    (hg : ∀ t, 0 ≤ g t) (hk : ∀ t, 0 ≤ k t) (h : ∀ t, c t ≤ f t + (g t + k t)) :
    √(∑ t, c t ^ 2) ≤ √(∑ t, f t ^ 2) + (√(∑ t, g t ^ 2) + √(∑ t, k t ^ 2)) := by
  have h1 := sqrt_sum_le univ f (fun t => g t + k t) c hf (fun t => add_nonneg (hg t) (hk t)) hc h
  have h2 := sqrt_sum_le univ g k (fun t => g t + k t) hg hk
    (fun t => add_nonneg (hg t) (hk t)) fun t => le_rfl
  linarith

/-- Pull-back of a length along a homomorphism. -/
def Len.comap {G H : Type*} [Group G] [Group H] (l : Len H) (φ : G →* H) : Len G where
  val g := l.val (φ g)
  one' := by rw [map_one, l.one']
  inv' g := by rw [map_inv, l.inv']
  mul' g h := by rw [map_mul]; exact l.mul' _ _

theorem Contr.comap {G H : Type*} [Group G] [Group H] {l : Len H} {m : ℕ} {s : ℝ}
    (h : Contr l m s) (φ : G →* H) : Contr (l.comap φ) m s := by
  intro τ hτ i
  exact h (fun M => φ (τ M)) (fun M N => by rw [hτ, map_mul]) i

/-- The root mean square of a length. -/
noncomputable def Len.rms {G : Type*} [Group G] [Fintype G] (l : Len G) : ℝ :=
  √((∑ g : G, l.val g ^ 2) / Fintype.card G)

theorem Len.rms_nonneg {G : Type*} [Group G] [Fintype G] (l : Len G) : 0 ≤ l.rms :=
  Real.sqrt_nonneg _

theorem Len.rms_sq {G : Type*} [Group G] [Fintype G] (l : Len G) :
    l.rms ^ 2 = (∑ g : G, l.val g ^ 2) / Fintype.card G :=
  Real.sq_sqrt (div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _))

/-- The mean square along a surjective homomorphism. -/
theorem Len.rms_comap {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H] (l : Len H)
    (φ : G →* H) (hφ : Function.Surjective φ) : (l.comap φ).rms = l.rms := by
  classical
  unfold Len.rms
  congr 1
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hH : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  rw [div_eq_div_iff hG.ne' hH.ne']
  have h1 : ∑ h : H, ∑ g : G, l.val (h * φ g) ^ 2 = Fintype.card G * ∑ h : H, l.val h ^ 2 := by
    rw [sum_comm]
    have e : ∀ g, ∑ h : H, l.val (h * φ g) ^ 2 = ∑ h : H, l.val h ^ 2 := fun g =>
      Equiv.sum_comp (Equiv.mulRight (φ g)) (fun h => l.val h ^ 2)
    rw [sum_congr rfl fun g _ => e g]
    simp
  have h2 : ∑ h : H, ∑ g : G, l.val (h * φ g) ^ 2 = Fintype.card H * ∑ g : G, l.val (φ g) ^ 2 := by
    have : ∀ h : H, ∑ g : G, l.val (h * φ g) ^ 2 = ∑ g : G, l.val (φ g) ^ 2 := by
      intro h
      obtain ⟨k, rfl⟩ := hφ h
      rw [← Equiv.sum_comp (Equiv.mulLeft k) (fun g => l.val (φ g) ^ 2)]
      exact sum_congr rfl fun g _ => by rw [Equiv.coe_mulLeft, map_mul]
    rw [sum_congr rfl fun h _ => this h]
    simp
  show (∑ g : G, l.val (φ g) ^ 2) * _ = _
  linarith

/-- The bound of Lemma lem:first for one n with the constant κ. -/
def Bd (m : ℕ) (s : ℝ) (n : ℕ) (κ : ℝ) : Prop :=
  ∀ l : Len (U n), Contr l m s → l.rms ≤ κ * l.S

theorem bd_one (m : ℕ) (s : ℝ) : Bd m s 1 0 := by
  intro l _
  have : ∀ g : U 1, g = 1 := by
    intro g
    apply mat_inj
    ext i j
    rw [Subsingleton.elim i j, mat_diag, mat_one, Matrix.one_apply_eq]
  have h : ∑ g : U 1, l.val g ^ 2 = 0 := sum_eq_zero fun g _ => by rw [this g, l.one']; simp
  rw [Len.rms, h]
  simp

theorem S_add_le {a b : ℕ} (l : Len (U (a + b))) :
    (l.comap (win (hl (a := a) (b := b)))).S + (l.comap (win (hr (a := a) (b := b)))).S ≤ l.S := by
  unfold Len.S
  have e1 : ∀ j, (l.comap (win (hl (a := a) (b := b)))).val (x a j) = l.val (x _ (wt hl j)) := by
    intro j
    show l.val (win hl (x a j)) = _
    rw [win_x]
  have e2 : ∀ j, (l.comap (win (hr (a := a) (b := b)))).val (x b j) = l.val (x _ (wt hr j)) := by
    intro j
    show l.val (win hr (x b j)) = _
    rw [win_x]
  rw [sum_congr rfl fun j _ => e1 j, sum_congr rfl fun j _ => e2 j]
  have i1 : Function.Injective (wt (hl (a := a) (b := b))) := by
    intro j j' h
    simpa [wt, Fin.ext_iff] using h
  have i2 : Function.Injective (wt (hr (a := a) (b := b))) := by
    intro j j' h
    simpa [wt, Fin.ext_iff] using h
  rw [← sum_image (s := univ) (g := wt (hl (a := a) (b := b))) (f := fun k => l.val (x _ k))
      (fun j _ j' _ h => i1 h),
    ← sum_image (s := univ) (g := wt (hr (a := a) (b := b))) (f := fun k => l.val (x _ k))
      (fun j _ j' _ h => i2 h), ← sum_union]
  · exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => l.nonneg _
  · rw [disjoint_left]
    intro k h1 h2
    simp only [mem_image, mem_univ, true_and] at h1 h2
    obtain ⟨j, rfl⟩ := h1
    obtain ⟨j', h⟩ := h2
    simp only [wt, Fin.ext_iff] at h
    omega

/-- The upper left block. -/
def tr {n n' : ℕ} (h : n ≤ n') : U n' →* U n where
  toFun A := mk (Matrix.of fun i j => mat A (Fin.castLE h i) (Fin.castLE h j))
    (fun i j hij => mat_lt A (by simpa using hij)) (fun i => mat_diag A _)
  map_one' := by
    apply mat_inj
    ext i j
    show (1 : Matrix _ _ F2) (Fin.castLE h i) (Fin.castLE h j) = (1 : Matrix _ _ F2) i j
    simp [Matrix.one_apply, Fin.ext_iff]
  map_mul' A B := by
    apply mat_inj
    ext i j
    show mat (A * B) (Fin.castLE h i) (Fin.castLE h j) = _
    rw [mat_mul, mat_mul, Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine sum_bij_ne_zero (fun k _ _ => Fin.castLE h k) (fun _ _ _ => mem_univ _)
      (fun k _ _ k' _ _ hk => by simpa [Fin.ext_iff] using hk) ?_ (fun _ _ _ => rfl)
    intro k _ hk
    have hkj : k ≤ Fin.castLE h j := by
      by_contra hlt
      rw [mat_lt B (not_le.1 hlt), mul_zero] at hk
      exact hk rfl
    have hkn : k.1 < n := lt_of_le_of_lt (Fin.le_def.1 hkj) j.2
    exact ⟨⟨k.1, hkn⟩, mem_univ _, hk, rfl⟩

theorem tr_apply {n n' : ℕ} (h : n ≤ n') (A : U n') (i j : Fin n) :
    mat (tr h A) i j = mat A (Fin.castLE h i) (Fin.castLE h j) := rfl

theorem tr_surjective {n n' : ℕ} (h : n ≤ n') : Function.Surjective (tr h) := by
  intro A
  refine ⟨win (p := 0) (by omega : 0 + n ≤ n') A, ?_⟩
  apply mat_inj
  ext i j
  have e : ∀ i : Fin n, Fin.castLE h i = we (p := 0) (by omega : 0 + n ≤ n') i := by
    intro i
    simp [we, Fin.ext_iff]
  rw [tr_apply, mat_win, e, e, wm, Matrix.add_apply, Matrix.sub_apply, wi_mul_we, wi_mul_we,
    Matrix.one_apply, Matrix.one_apply]
  simp [we_inj]

theorem bd_mono {m : ℕ} {s : ℝ} {n n' : ℕ} (h : n ≤ n') {κ : ℝ} (hκ : 0 ≤ κ) (hB : Bd m s n' κ) :
    Bd m s n κ := by
  intro l hC
  have h1 := hB (l.comap (tr h)) (hC.comap _)
  rw [Len.rms_comap _ _ (tr_surjective h)] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hκ)
  unfold Len.S
  have e : ∀ j : Fin (n' - 1), (l.comap (tr h)).val (x n' j) =
      if hj : j.1 < n - 1 then l.val (x n ⟨j.1, hj⟩) else 0 := by
    intro j
    show l.val (tr h (x n' j)) = _
    split_ifs with hj
    · congr 1
      apply mat_inj
      ext a b
      rw [tr_apply, mat_x, mat_x]
      simp [Matrix.one_apply, Matrix.single_apply, lo, hi, Fin.ext_iff]
    · have : tr h (x n' j) = 1 := by
        apply mat_inj
        ext a b
        rw [tr_apply, mat_x, mat_one]
        have : ¬ (j.1 = a.1 ∧ j.1 + 1 = b.1) := by
          have := b.2
          omega
        simp [Matrix.one_apply, Matrix.single_apply, lo, hi, Fin.ext_iff, this]
      rw [this, l.one']
  rw [sum_congr rfl fun j _ => e j]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun j : Fin (n' - 1) => j.1 < n - 1)]
  rw [Finset.sum_eq_zero (s := univ.filter fun j : Fin (n' - 1) => ¬ j.1 < n - 1), add_zero]
  · refine le_of_eq ?_
    refine sum_bij' (fun j hj => ⟨j.1, by simpa using hj⟩)
      (fun j _ => ⟨j.1, by have := j.2; omega⟩) ?_ ?_ ?_ ?_ ?_
    · intro j _
      exact mem_univ _
    · intro j _
      simp
    · intro j _
      rfl
    · intro j _
      rfl
    · intro j hj
      have : j.1 < n - 1 := by simpa using hj
      simp [this]
  · intro j hj
    have : ¬ j.1 < n - 1 := by simpa using hj
    simp [this]

end Nc.Flag

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Windows of the unitriangular group acting on a complete CAT(0) space
-/

open Finset Matrix

namespace Nc.Flag

open Cat
open Nc.Tower (U SL2 lo hi x)

variable {h : ℕ}

/-- A smaller window. -/
theorem win_win {p n p' n' : ℕ} (hp : p + n ≤ h) (hp' : p' + n' ≤ n) (hpp : p + p' + n' ≤ h)
    (A : U n') : win hp (win hp' A) = win hpp A := by
  apply mat_inj
  rw [mat_win, mat_win, mat_win]
  have e : wi hp * wi hp' = wi hpp := by
    ext i j
    simp only [Matrix.mul_apply, wi, Matrix.of_apply]
    rw [sum_eq_single (we hp' j)]
    · have : we hp (we hp' j) = we hpp j := by
        simp only [we, Fin.ext_iff]
        omega
      simp [this]
    · intro c _ hc
      simp [hc]
    · simp
  unfold wm
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, ← e, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  abel

theorem wi_disj {p n p' n' : ℕ} (hp : p + n ≤ h) (hp' : p' + n' ≤ h) (hd : p + n ≤ p') :
    (wi hp)ᵀ * wi hp' = 0 := by
  ext i j
  simp only [Matrix.mul_apply, wi, Matrix.of_apply, Matrix.transpose_apply, Matrix.zero_apply]
  refine sum_eq_zero fun k _ => ?_
  by_cases h1 : k = we hp i
  · have h2 : k ≠ we hp' j := by
      rw [h1]
      simp only [we, ne_eq, Fin.ext_iff]
      omega
    simp [h2]
  · simp [h1]

/-- Disjoint windows commute. -/
theorem win_comm {p n p' n' : ℕ} (hp : p + n ≤ h) (hp' : p' + n' ≤ h) (hd : p + n ≤ p')
    (A : U n) (B : U n') : win hp A * win hp' B = win hp' B * win hp A := by
  apply mat_inj
  rw [mat_mul, mat_mul, mat_win, mat_win]
  have h1 := wi_disj hp hp' hd
  have h2 : (wi hp')ᵀ * wi hp = 0 := by
    rw [← Matrix.transpose_transpose (wi hp), ← Matrix.transpose_mul, h1, Matrix.transpose_zero]
  have z1 : ∀ (X : Matrix (Fin n) (Fin n) F2) (Y : Matrix (Fin n') (Fin n') F2),
      wi hp * X * (wi hp)ᵀ * (wi hp' * Y * (wi hp')ᵀ) = 0 := by
    intro X Y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((wi hp)ᵀ) (wi hp'), h1]
    simp
  have z2 : ∀ (X : Matrix (Fin n) (Fin n) F2) (Y : Matrix (Fin n') (Fin n') F2),
      wi hp' * Y * (wi hp')ᵀ * (wi hp * X * (wi hp)ᵀ) = 0 := by
    intro X Y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((wi hp')ᵀ) (wi hp), h2]
    simp
  unfold wm
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, z1, z2]
  simp only [Matrix.mul_one, Matrix.one_mul]
  abel

/-- The homomorphism of a window (trivial if it doesn't fit). -/
def wh (h p n : ℕ) : U n →* U h := if hp : p + n ≤ h then win hp else 1

theorem wh_eq {p n : ℕ} (hp : p + n ≤ h) : wh h p n = win hp := dif_pos hp

variable {Z : Type*} [MetricSpace Z] (A : IsoAct (U h) Z)

namespace IsoAct

/-- The action of a window. -/
def W (p n : ℕ) : IsoAct (U n) Z := A.comap (wh h p n)

/-- The displacement by a generator. -/
noncomputable def e (j : ℕ) (z : Z) : ℝ :=
  if hj : j < h - 1 then dist z (A.act (x h ⟨j, hj⟩) z) else 0

theorem e_nonneg (j : ℕ) (z : Z) : 0 ≤ A.e j z := by
  unfold e
  split_ifs
  · exact dist_nonneg
  · exact le_rfl

theorem Fix.sub {p n p' n' : ℕ} {z : Z} (hz : (A.W p n).Fix z) (h1 : p ≤ p')
    (h2 : p' + n' ≤ p + n) (h3 : p + n ≤ h) : (A.W p' n').Fix z := by
  intro g
  have e1 : wh h p' n' g = wh h p n (win (p := p' - p) (n := n') (h := n) (by omega) g) := by
    rw [wh_eq (by omega), wh_eq h3, win_win h3 (by omega) (by omega)]
    have : p + (p' - p) = p' := by omega
    congr! 2
    exact this.symm
  show A.act (wh h p' n' g) z = z
  rw [e1]
  exact hz _

theorem wh_comm {p n p' n' : ℕ} (hd : p + n ≤ p') (hp' : p' + n' ≤ h) (a : U n) (b : U n') :
    wh h p n a * wh h p' n' b = wh h p' n' b * wh h p n a := by
  rw [wh_eq (by omega), wh_eq hp', win_comm _ _ hd]

theorem wh_x {j : ℕ} (hj : j < h - 1) : wh h j 2 (x 2 ⟨0, by omega⟩) = x h ⟨j, hj⟩ := by
  rw [wh_eq (by omega), win_x]
  rfl

theorem e_zero {p n j : ℕ} {z : Z} (hz : (A.W p n).Fix z) (h1 : p ≤ j) (h2 : j + 2 ≤ p + n)
    (h3 : p + n ≤ h) : A.e j z = 0 := by
  have hj : j < h - 1 := by omega
  have h4 := hz.sub A h1 h2 h3
  unfold e
  rw [dif_pos hj, ← wh_x hj]
  have := h4 (x 2 ⟨0, by omega⟩)
  rw [show A.act (wh h j 2 (x 2 ⟨0, by omega⟩)) z = z from this, dist_self]

theorem e_le {p n j : ℕ} {y : Z} (hy : (A.W p n).Fix y) (h1 : p ≤ j) (h2 : j + 2 ≤ p + n)
    (h3 : p + n ≤ h) (z : Z) : A.e j z ≤ 2 * dist z y := by
  have hj : j < h - 1 := by omega
  have h4 := hy.sub A h1 h2 h3 (x 2 ⟨0, by omega⟩)
  have h5 : A.act (x h ⟨j, hj⟩) y = y := by rw [← wh_x hj]; exact h4
  unfold e
  rw [dif_pos hj]
  refine (dist_triangle z y _).trans ?_
  conv_lhs => rw [← h5]
  rw [A.iso', h5, dist_comm y z]
  linarith

end IsoAct

end Nc.Flag

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# One step of the averaging of projections: the arithmetic
-/

open Finset

namespace Nc.Flag

open Cat
open Nc.Tower (U SL2 lo hi x)

/-- One step of the averaging. -/
theorem step_num {X Y d L δ : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hL : 1 ≤ L) (hδ : 0 < δ)
    (h1 : Y ^ 2 ≤ (1 - δ / L) * X ^ 2) (h2 : L * d ^ 2 ≤ X ^ 2 - Y ^ 2) :
    d ≤ 2 / √δ * (X - Y) := by
  have hL0 : 0 < L := by linarith
  have h3 : δ * X ^ 2 ≤ L * (X ^ 2 - Y ^ 2) := by
    have h4 := mul_le_mul_of_nonneg_left h1 hL0.le
    have h5 : L * ((1 - δ / L) * X ^ 2) = L * X ^ 2 - δ * X ^ 2 := by field_simp
    rw [h5] at h4
    linarith
  have hYX : Y ≤ X := by
    refine (abs_le_of_sq_le_sq' (show Y ^ 2 ≤ X ^ 2 from ?_) hX).2
    have : 0 ≤ δ * X ^ 2 := by positivity
    have h6 : 0 ≤ X ^ 2 - Y ^ 2 := by
      by_contra h7
      push Not at h7
      have := mul_neg_of_pos_of_neg hL0 h7
      linarith
    linarith
  have hs : 0 < √δ := Real.sqrt_pos.2 hδ
  rcases hX.eq_or_lt with rfl | hX0
  · have hY0 : Y = 0 := le_antisymm hYX hY
    subst hY0
    have : d ^ 2 ≤ 0 := by
      by_contra h6
      push Not at h6
      have := mul_pos hL0 h6
      linarith
    have : d = 0 := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _))
    rw [this]
    simp
  · have h4 : δ * X ^ 2 * (L * d ^ 2) ≤ L * (4 * X ^ 2 * (X - Y) ^ 2) := by
      have e1 : 0 ≤ X ^ 2 - Y ^ 2 := by nlinarith
      calc δ * X ^ 2 * (L * d ^ 2) ≤ (L * (X ^ 2 - Y ^ 2)) * (X ^ 2 - Y ^ 2) :=
            mul_le_mul h3 h2 (by positivity) (by positivity)
        _ = L * ((X + Y) ^ 2 * (X - Y) ^ 2) := by ring
        _ ≤ L * (4 * X ^ 2 * (X - Y) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hL0.le
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            nlinarith
    have h5 : δ * d ^ 2 ≤ 4 * (X - Y) ^ 2 := by
      have h6 : (L * X ^ 2) * (δ * d ^ 2) ≤ (L * X ^ 2) * (4 * (X - Y) ^ 2) := by linarith
      exact le_of_mul_le_mul_left h6 (by positivity)
    have h6 : (√δ * d) ^ 2 ≤ (2 * (X - Y)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hδ.le]
      linarith
    have h7 := (abs_le_of_sq_le_sq' h6 (by linarith)).2
    rw [div_mul_eq_mul_div, le_div_iff₀ hs]
    linarith

end Nc.Flag

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The choice of the size of the windows
-/

open Finset Filter Topology

namespace Nc.Flag

theorem exists_log_large {ρ ε : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) (hε : 0 < ε) :
    ∃ L0 : ℕ, ∀ L ≥ L0, ((L : ℝ) + 1) ^ 4 * ρ ^ L ≤ ε := by
  have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one 4 (r := ρ) (by rw [abs_of_pos h0]; exact h1)
  have h2 := (h.eventually (gt_mem_nhds (show (0 : ℝ) < ε * ρ by positivity)))
  obtain ⟨N, hN⟩ := eventually_atTop.1 h2
  refine ⟨N, fun L hL => ?_⟩
  have h3 := hN (L + 1) (by omega)
  push_cast at h3
  have h4 : ((L : ℝ) + 1) ^ 4 * ρ ^ L * ρ < ε * ρ := by
    calc _ = ((L : ℝ) + 1) ^ 4 * ρ ^ (L + 1) := by rw [pow_succ]; ring
      _ < _ := h3
  exact (lt_of_mul_lt_mul_right h4 h0.le).le

end Nc.Flag

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Translations of maps of a group into a metric space; what is used of prices
-/

open Finset Matrix

namespace Nc.Flag

open Cat

/-! ### Maps of a group into a complete CAT(0) space -/

section Maps
variable {G : Type} [Group G] [Fintype G] {Y : Type} [MetricSpace Y]

/-- Translations of maps. -/
def transAct (G Y : Type) [Group G] [Fintype G] [MetricSpace Y] :
    IsoAct G (PiLp 2 fun _ : G => Y) where
  act g z := WithLp.toLp 2 fun k => z (g⁻¹ * k)
  one' z := by
    ext k
    simp
  mul' g h z := by
    ext k
    simp [mul_assoc]
  iso' g z z' := by
    have h1 : dist (WithLp.toLp 2 fun k => z (g⁻¹ * k) : PiLp 2 fun _ : G => Y)
        (WithLp.toLp 2 fun k => z' (g⁻¹ * k)) ^ 2 = dist z z' ^ 2 := by
      rw [piLp_dist_sq, piLp_dist_sq]
      exact Equiv.sum_comp (Equiv.mulLeft g⁻¹) (fun k => dist (z k) (z' k) ^ 2)
    exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 h1

theorem transAct_dist (z : PiLp 2 fun _ : G => Y) (g : G) :
    dist z ((transAct G Y).act g z) ^ 2 = ∑ k, dist (z (g * k)) (z k) ^ 2 := by
  rw [piLp_dist_sq, ← Equiv.sum_comp (Equiv.mulLeft g)]
  refine sum_congr rfl fun k _ => ?_
  show dist (z (g * k)) (z (g⁻¹ * (g * k))) ^ 2 = _
  rw [inv_mul_cancel_left]

end Maps

/-! ### Prices -/

variable {Pr : ∀ V : Type, (V → V → ℝ) → Prop}

end Nc.Flag

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, subsection "Lengths": the remark on maps into price spaces, polynomial growth and rank one

The third lemma of the subsection (lem:first) is in Paper/Groups.lean.
-/

namespace Paper

open Finset Nc.Flag Nc.Price
open Nc.Tower (U x lo hi)

/-- The mean of f² over the matrices of rank r. -/
noncomputable def rankMean {k : ℕ} (f : Mt k → ℝ) (r : ℕ) : ℝ :=
  (∑ W ∈ (univ : Finset (Mt k)).filter (fun W => W.rank = r), f W ^ 2) /
    ((univ : Finset (Mt k)).filter (fun W => W.rank = r)).card

theorem rankMean_nonneg {k : ℕ} (f : Mt k → ℝ) (r : ℕ) : 0 ≤ rankMean f r :=
  div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

theorem DM_eq_rankMean {k : ℕ} (f : Mt k → ℝ) (S : Finset (Fin k)) :
    DM f (dg S) = (Fintype.card (GLM (Fin k)) : ℝ) ^ 2 * rankMean f S.card := by
  have hn : (0 : ℝ) < ((univ : Finset (Mt k)).filter fun W => W.rank = S.card).card := by
    exact_mod_cast card_pos.2 ⟨dg S, mem_filter.2 ⟨mem_univ _, rank_dg S⟩⟩
  rw [rankMean, ← mul_div_assoc, eq_div_iff hn.ne', mul_comm]
  exact card_mul_DM f S

/-- A length contracts: "for every homomorphism τ from the additive group Mat_μ(F₂) into the group, the mean of |τW|²
over rank μ is at most s² times that over rank 1". It is the project's Contr. -/
theorem contracts_iff {G : Type} [Group G] (l : Len G) {μ : ℕ} (hμ : 1 ≤ μ) (s : ℝ) :
    Contr l μ s ↔ ∀ τ : Mt μ → G, (∀ M N, τ (M + N) = τ M * τ N) →
      rankMean (fun W => l.val (τ W)) μ ≤ s ^ 2 * rankMean (fun W => l.val (τ W)) 1 := by
  have hg : (0 : ℝ) < (Fintype.card (GLM (Fin μ)) : ℝ) ^ 2 := by
    have : (0 : ℝ) < Fintype.card (GLM (Fin μ)) := by exact_mod_cast Fintype.card_pos
    positivity
  have key : ∀ (f : Mt μ → ℝ) (i : Fin μ),
      DM f (dg univ) ≤ s ^ 2 * DM f (dg {i}) ↔ rankMean f μ ≤ s ^ 2 * rankMean f 1 := fun f i => by
    rw [DM_eq_rankMean, DM_eq_rankMean, card_singleton, card_univ, Fintype.card_fin, mul_left_comm,
      mul_le_mul_iff_right₀ hg]
  exact ⟨fun h τ hτ => (key _ ⟨0, hμ⟩).1 (h τ hτ _), fun h τ hτ i => (key _ i).2 (h τ hτ)⟩

/-- A multiple of a contracting length contracts. -/
theorem contracts_smul {G : Type} [Group G] (l l' : Len G) {μ : ℕ} (hμ : 1 ≤ μ) {s : ℝ} {c : ℝ}
    (h : ∀ g, l'.val g = c * l.val g) (hl : Contr l μ s) : Contr l' μ s := by
  refine (contracts_iff l' hμ s).2 fun τ hτ => ?_
  have e : ∀ r, rankMean (fun W => l'.val (τ W)) r = c ^ 2 * rankMean (fun W => l.val (τ W)) r := fun r => by
    simp only [rankMean, h, mul_pow, ← Finset.mul_sum, mul_div_assoc]
  rw [e, e, mul_left_comm (s ^ 2)]
  exact mul_le_mul_of_nonneg_left ((contracts_iff l hμ s).1 hl τ hτ) (sq_nonneg c)

/-- The remark after the definition of contracting lengths: "If a map f sends a finite group into a price space, then
|g| = (E_a|f(a)f(ga)|²)^(1/2) contracts: pull the price back along W ↦ f(τ(W)a) and average over a." -/
theorem lengths_of_maps {K : Type} [Field K] {μ : ℕ} {s : ℝ} (hμ : 1 ≤ μ) (hs : 0 ≤ s)
    (hcase : ∀ w : Mt μ → Mt μ → ℝ, IsPrice K w → distAtRank w μ ≤ s * distAtRank w 1)
    {G : Type} [Group G] [Fintype G] {Y : Type} [MetricSpace Y] (hY : IsPrice K fun a b : Y => dist a b)
    (f : G → Y) :
    ∃ l : Len G, (∀ g, l.val g = √((∑ a, dist (f a) (f (g * a)) ^ 2) / Fintype.card G)) ∧ Contr l μ s := by
  have hc : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  set l0 : Len G := (transAct G Y).len (WithLp.toLp 2 f) with hl0
  have hl : ∀ g, l0.val g ^ 2 = ∑ a, dist (f a) (f (g * a)) ^ 2 := fun g => by
    rw [hl0, IsoAct.len_val, transAct_dist]
    exact sum_congr rfl fun a _ => by rw [dist_comm]
  let l : Len G :=
    { val := fun g => l0.val g / √(Fintype.card G : ℝ)
      one' := by simp [l0.one']
      inv' := fun g => by rw [l0.inv']
      mul' := fun g g' => by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (l0.mul' g g') (Real.sqrt_nonneg _) }
  refine ⟨l, fun g => ?_, (contracts_iff l hμ s).2 fun τ hτ => ?_⟩
  · rw [Real.sqrt_div' _ hc.le, ← hl, Real.sqrt_sq (l0.nonneg g)]
  have e : ∀ r, rankMean (fun W => l.val (τ W)) r =
      (∑ k : G, meanSq (fun a b => dist (f (τ a * k)) (f (τ b * k))) r) / Fintype.card G := by
    intro r
    have h1 : ∀ W, l.val (τ W) ^ 2 = l0.val (τ W) ^ 2 / Fintype.card G := fun W => by
      show (l0.val (τ W) / √(Fintype.card G : ℝ)) ^ 2 = _
      rw [div_pow, Real.sq_sqrt hc.le]
    have h2 : ∀ (W a : Mt μ), ∑ k : G, dist (f (τ a * k)) (f (τ (a + W) * k)) ^ 2 = l0.val (τ W) ^ 2 := by
      intro W a
      rw [hl, ← Equiv.sum_comp (Equiv.mulLeft (τ a)) (fun k => dist (f k) (f (τ W * k)) ^ 2)]
      refine sum_congr rfl fun k _ => ?_
      rw [add_comm a W, hτ, mul_assoc]
      rfl
    simp only [rankMean, meanSq, h1, ← Finset.sum_div]
    rw [Finset.sum_comm, sum_congr rfl fun a _ => Finset.sum_comm]
    simp only [h2, sum_const, card_univ, nsmul_eq_mul]
    have hM : (Fintype.card (Mt μ) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  have h3 : ∀ k : G, meanSq (fun a b => dist (f (τ a * k)) (f (τ b * k))) μ ≤
      s ^ 2 * meanSq (fun a b => dist (f (τ a * k)) (f (τ b * k))) 1 := fun k => by
    have := hcase _ (hY.comp fun a => f (τ a * k))
    rwa [distAtRank, distAtRank, Real.sqrt_le_left (mul_nonneg hs (Real.sqrt_nonneg _)), mul_pow,
      Real.sq_sqrt (meanSq_nonneg _ _)] at this
  rw [e, e, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right ((sum_le_sum fun k _ => h3 k).trans_eq (mul_sum _ _ _).symm) hc.le

/-- The proof of Lemma lem:growth: "Compose τ with Z ↦ α(Z ⊗ 1_i)α′ … and average: D(μi) ≤ sD(i) if μi ≤ k." -/
theorem lem_growth_digit {G : Type} [Group G] (l : Len G) {μ : ℕ} {s : ℝ} (hμ : 1 ≤ μ) (hs : 0 ≤ s)
    (hl : Contr l μ s) {k : ℕ} (τ : Mt k → G) (hτ : ∀ M N, τ (M + N) = τ M * τ N) {i : ℕ} (hi : μ * i ≤ k) :
    √(rankMean (fun W => l.val (τ W)) (μ * i)) ≤ s * √(rankMean (fun W => l.val (τ W)) i) := by
  set f : Mt k → ℝ := fun W => l.val (τ W)
  have hg : (0 : ℝ) < (Fintype.card (GLM (Fin k)) : ℝ) ^ 2 := by
    have : (0 : ℝ) < Fintype.card (GLM (Fin k)) := by exact_mod_cast Fintype.card_pos
    positivity
  obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin k))) (n := μ * i) (by simpa using hi)
  let e : Fin μ × Fin i ↪ Fin k := (finProdFinEquiv.trans (Fintype.equivOfCardEq (α := Fin (μ * i))
    (β := {j // j ∈ S}) (by simp [hS]))).toEmbedding.trans (Function.Embedding.subtype _)
  have h := (good_of_contr l hl τ hτ).digit i e ⟨0, hμ⟩
  rw [DM_eq_rankMean, DM_eq_rankMean, card_map, card_map, card_univ, card_product, card_singleton, card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, one_mul, mul_left_comm] at h
  rw [← Real.sqrt_sq hs, ← Real.sqrt_mul (sq_nonneg s)]
  exact Real.sqrt_le_sqrt (le_of_mul_le_mul_left h hg)

/-- The proof of Lemma lem:growth: "By Minkowski's inequality D(i+i′) ≤ D(i) + D(i′)." -/
theorem lem_growth_minkowski {G : Type} [Group G] (l : Len G) {k : ℕ} (τ : Mt k → G)
    (hτ : ∀ M N, τ (M + N) = τ M * τ N) {i i' : ℕ} (hi : i + i' ≤ k) :
    √(rankMean (fun W => l.val (τ W)) (i + i')) ≤
      √(rankMean (fun W => l.val (τ W)) i) + √(rankMean (fun W => l.val (τ W)) i') := by
  set f : Mt k → ℝ := fun W => l.val (τ W)
  have hg : (0 : ℝ) < Fintype.card (GLM (Fin k)) := by exact_mod_cast Fintype.card_pos
  obtain ⟨U, -, hU⟩ := exists_subset_card_eq (s := (univ : Finset (Fin k))) (n := i + i') (by simpa using hi)
  obtain ⟨S, hSU, hS⟩ := exists_subset_card_eq (s := U) (n := i) (by omega)
  have h := DM_dg_le f (fun _ => l.nonneg _) (fun M N => by simp only [f, hτ]; exact l.mul' _ _)
    (S := S) (T := U \ S) disjoint_sdiff
  rw [union_sdiff_of_subset hSU, DM_eq_rankMean, DM_eq_rankMean, DM_eq_rankMean, card_sdiff_of_subset hSU, hU, hS,
    Nat.add_sub_cancel_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq hg.le, ← mul_add] at h
  exact le_of_mul_le_mul_left h hg

/-- **Paper: Lemma lem:growth.** "Let 1 ≤ r ≤ k, let τ be a homomorphism from Mat_{k×k}(F₂) into a group with a
contracting length, and let D(r) be the quadratic mean of |τW| over rank r. Then D(r) ≤ μ(j+1)s^j D(1), where
j = ⌊log_μ r⌋." (r = 0 is allowed too.) -/
theorem lem_growth {G : Type} [Group G] (l : Len G) {μ : ℕ} {s : ℝ} (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hl : Contr l μ s)
    {k : ℕ} (τ : Mt k → G) (hτ : ∀ M N, τ (M + N) = τ M * τ N) {r : ℕ} (hr : r ≤ k) :
    √(rankMean (fun W => l.val (τ W)) r) ≤
      (μ : ℝ) * (Nat.log μ r + 1) * s ^ Nat.log μ r * √(rankMean (fun W => l.val (τ W)) 1) := by
  set D : ℕ → ℝ := fun r => √(rankMean (fun W => l.val (τ W)) r) with hD
  show D r ≤ (μ : ℝ) * (Nat.log μ r + 1) * s ^ Nat.log μ r * D 1
  have hD0 : D 0 = 0 := by
    have h := (good_of_contr l hl τ hτ).dg_zero
    have hg : ((Fintype.card (GLM (Fin k)) : ℝ)) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    rw [DM_eq_rankMean, card_empty, mul_eq_zero, or_iff_right hg] at h
    simp only [hD, h, Real.sqrt_zero]
  have hD1 : 0 ≤ D 1 := Real.sqrt_nonneg _
  have hsmall : ∀ t, t ≤ k → D t ≤ t * D 1 := by
    intro t
    induction t with
    | zero => intro _; simp [hD0]
    | succ t ih =>
      intro ht
      refine (lem_growth_minkowski l τ hτ ht).trans ?_
      have := ih (by omega)
      push_cast
      linarith
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    by_cases hrm : r < μ
    · refine (hsmall r hr).trans ?_
      rw [Nat.log_of_lt hrm]
      have : (r : ℝ) ≤ μ := by exact_mod_cast hrm.le
      simp only [CharP.cast_eq_zero, zero_add, mul_one, pow_zero]
      gcongr
    · push Not at hrm
      have hq : r / μ < r := Nat.div_lt_self (by omega) (by omega)
      have hm : r % μ ≤ μ := (Nat.mod_lt r (by omega)).le
      have h1 : D r ≤ D (μ * (r / μ)) + D (r % μ) := by
        have := lem_growth_minkowski l τ hτ (i := μ * (r / μ)) (i' := r % μ) (by rw [Nat.div_add_mod]; exact hr)
        rwa [Nat.div_add_mod] at this
      have h2 : D (μ * (r / μ)) ≤ s * D (r / μ) :=
        lem_growth_digit l (by omega) (by linarith) hl τ hτ ((Nat.mul_div_le r μ).trans hr)
      have h3 := mul_le_mul_of_nonneg_left (ih _ hq (by omega)) (show 0 ≤ s by linarith)
      have hmR : ((r % μ : ℕ) : ℝ) ≤ μ := by exact_mod_cast hm
      have h4 : D (r % μ) ≤ μ * D 1 :=
        (hsmall _ (by have := Nat.mod_le r μ; omega)).trans (mul_le_mul_of_nonneg_right hmR hD1)
      have hlog : Nat.log μ r = Nat.log μ (r / μ) + 1 := Nat.log_of_one_lt_of_le (by omega) hrm
      have hp : 1 ≤ s ^ (Nat.log μ (r / μ) + 1) := one_le_pow₀ hs
      have h5 : (μ : ℝ) * D 1 ≤ μ * D 1 * s ^ (Nat.log μ (r / μ) + 1) := le_mul_of_one_le_right (by positivity) hp
      rw [hlog]
      push_cast
      refine (h1.trans (add_le_add (h2.trans h3) (h4.trans h5))).trans (le_of_eq ?_)
      ring

/-- **Paper: Lemma lem:words.** "For 1 ≤ k < n and nonzero ξ, ω the element of U_n with upper right block ξωᵀ and unit
diagonal blocks has, in every length on U_n, length at most 18 ∑_j |x_j|." -/
theorem lem_words {n : ℕ} (l : Len (U n)) (k : ℕ) (u φ : Fin n → F2) (hu : ∀ i, u i ≠ 0 → i.1 < k)
    (hφk : ∀ j, φ j ≠ 0 → k ≤ j.1) (A : U n) (hA : mat A = 1 + Matrix.vecMulVec u φ) :
    l.val A ≤ 18 * ∑ j : Fin (n - 1), l.val (x n j) := by
  show l.val A ≤ 18 * l.S
  have hs : ∀ i j, u i ≠ 0 → φ j ≠ 0 → i < j := fun i j hi hj =>
    Fin.lt_def.2 (by have := hu i hi; have := hφk j hj; omega)
  have hS := l.S_nonneg
  have f2 : ∀ a : F2, a ≠ 0 → a = 1 := by decide
  by_cases h0 : (∃ i, u i ≠ 0) ∧ ∃ j, φ j ≠ 0
  · obtain ⟨⟨i0, hi0⟩, j0, hj0⟩ := h0
    obtain ⟨a, ha, hmax⟩ := exists_max_image (univ.filter fun i => u i ≠ 0) id
      ⟨i0, by simpa using hi0⟩
    have ha0 : u a ≠ 0 := by simpa using ha
    have ha1 : ∀ i, a < i → u i = 0 := by
      intro i hi
      by_contra h
      exact absurd (hmax i (by simpa using h)) (not_le.2 hi)
    have haj := hs a j0 ha0 hj0
    rw [Fin.lt_def] at haj
    have hj0n := j0.2
    set j : Fin (n - 1) := ⟨a.1, by omega⟩ with hj
    have hlo : lo j = a := rfl
    have hφ : ∀ i, i < hi j → φ i = 0 := by
      intro i hi
      by_contra h
      have h1 := hs a i ha0 h
      rw [Fin.lt_def] at h1 hi
      simp only [Nc.Tower.hi, hj] at hi
      omega
    by_cases hb : φ (hi j) = 0
    · have huhi : ∀ i, u i ≠ 0 → i < hi j := by
        intro i hi
        have h1 : i ≤ a := not_lt.1 fun h => hi (ha1 i h)
        exact lt_of_le_of_lt h1 (hlo ▸ Nc.Tower.lo_lt_hi j)
      have key : ∀ ψ : Fin n → F2, (∀ i, i < hi j → ψ i = 0) → ψ (hi j) = 1 →
          ∃ B : U n, mat B = 1 + Matrix.vecMulVec u ψ ∧ l.val B ≤ 9 * l.S := by
        intro ψ h1 h2
        have hz : ∀ i k, k ≤ i → u i * ψ k = 0 := by
          intro i k hki
          by_cases hi : u i = 0
          · rw [hi, zero_mul]
          · rw [h1 k (lt_of_le_of_lt hki (huhi i hi)), mul_zero]
        let B : U n := mk (1 + Matrix.vecMulVec u ψ)
          (fun i k hki => by
            rw [Matrix.add_apply, Matrix.one_apply_ne hki.ne', Matrix.vecMulVec_apply, hz i k hki.le,
              add_zero])
          (fun i => by
            rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.vecMulVec_apply, hz i i le_rfl,
              add_zero])
        exact ⟨B, rfl, lead_le l j u ψ (f2 _ ha0) ha1 h2 h1 B rfl⟩
      obtain ⟨B, hB, hlB⟩ := key (Pi.single (hi j) 1) (fun i hi => Pi.single_eq_of_ne hi.ne _)
        (Pi.single_eq_same _ _)
      obtain ⟨C, hC, hlC⟩ := key (φ + Pi.single (hi j) 1)
        (fun i hi => by rw [Pi.add_apply, hφ i hi, Pi.single_eq_of_ne hi.ne, add_zero])
        (by rw [Pi.add_apply, hb, Pi.single_eq_same, zero_add])
      have hABC : A = B * C := by
        apply mat_inj
        rw [mat_mul, hA, hB, hC, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one,
          Matrix.vecMulVec_add]
        have : Matrix.vecMulVec u (Pi.single (hi j) (1 : F2)) *
            (Matrix.vecMulVec u φ + Matrix.vecMulVec u (Pi.single (hi j) 1)) = 0 := by
          rw [← Matrix.vecMulVec_add]
          ext i m
          rw [Matrix.mul_apply]
          refine sum_eq_zero fun c _ => ?_
          simp only [Matrix.vecMulVec_apply]
          by_cases hc : c = hi j
          · have : u c = 0 := by
              by_contra h
              exact absurd (huhi c h) (by rw [hc]; exact lt_irrefl _)
            rw [this]; simp
          · rw [Pi.single_eq_of_ne hc]; simp
        rw [this, add_zero]
        ext i m
        simp only [Matrix.add_apply, Matrix.vecMulVec_apply]
        have := f2_add_self (u i * (Pi.single (hi j) 1 : Fin n → F2) m)
        linear_combination (-1 : F2) * this
      rw [hABC]
      have := l.mul' B C
      linarith
    · have := lead_le l j u φ (f2 _ ha0) ha1 (f2 _ hb) hφ A hA
      linarith
  · have : mat A = 1 := by
      rw [hA]
      ext i k
      rw [Matrix.add_apply, Matrix.vecMulVec_apply]
      by_cases h1 : u i = 0
      · rw [h1, zero_mul, add_zero]
      · have : φ k = 0 := by
          by_contra h
          exact h0 ⟨⟨i, h1⟩, k, h⟩
        rw [this, mul_zero, add_zero]
    have hA1 : A = 1 := mat_inj (this.trans mat_one.symm)
    rw [hA1, l.one']
    linarith

end Paper

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The unitriangular group is generated by the x_j
-/

open Finset Matrix

namespace Nc.Flag

open Nc.Tower (U SL2 lo hi x)

variable {h : ℕ}

open Classical in
/-- The length function of a subgroup: 0 in it, 1 outside. -/
noncomputable def subLen {G : Type*} [Group G] (H : Subgroup G) : Len G where
  val g := if g ∈ H then 0 else 1
  one' := if_pos H.one_mem
  inv' g := by
    by_cases hg : g ∈ H
    · rw [if_pos hg, if_pos (H.inv_mem hg)]
    · rw [if_neg hg, if_neg fun h => hg (by simpa using H.inv_mem h)]
  mul' a b := by
    by_cases ha : a ∈ H
    · by_cases hb : b ∈ H
      · rw [if_pos ha, if_pos hb, if_pos (H.mul_mem ha hb)]
        norm_num
      · rw [if_pos ha, if_neg hb]
        split_ifs <;> norm_num
    · rw [if_neg ha]
      split_ifs <;> norm_num

/-- The element with the columns ≥ c replaced by those of 1. -/
def colCut (A : U h) (c : ℕ) : U h :=
  mk (Matrix.of fun i j => if j.1 < c then mat A i j else (1 : Matrix (Fin h) (Fin h) F2) i j)
    (fun i j hij => by
      simp only [Matrix.of_apply]
      split_ifs
      · exact mat_lt A hij
      · exact Matrix.one_apply_ne hij.ne')
    (fun i => by
      simp only [Matrix.of_apply]
      split_ifs
      · exact mat_diag A i
      · exact Matrix.one_apply_eq i)

theorem colCut_apply (A : U h) (c : ℕ) (i j : Fin h) :
    mat (colCut A c) i j = if j.1 < c then mat A i j else (1 : Matrix (Fin h) (Fin h) F2) i j := rfl

/-- The elementary column. -/
def colEl (A : U h) (c : Fin h) : U h :=
  mk (1 + Matrix.vecMulVec (fun i => if i < c then mat A i c else 0) (Pi.single c 1))
    (fun i j hij => by
      rw [Matrix.add_apply, Matrix.one_apply_ne hij.ne', Matrix.vecMulVec_apply, zero_add]
      by_cases hj : j = c
      · subst hj
        rw [if_neg (not_lt.2 hij.le), zero_mul]
      · rw [Pi.single_eq_of_ne hj, mul_zero])
    (fun i => by
      rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.vecMulVec_apply]
      by_cases hj : i = c
      · subst hj
        rw [if_neg (lt_irrefl _), zero_mul, add_zero]
      · rw [Pi.single_eq_of_ne hj, mul_zero, add_zero])

theorem mat_colEl (A : U h) (c : Fin h) : mat (colEl A c) =
    1 + Matrix.vecMulVec (fun i => if i < c then mat A i c else 0) (Pi.single c 1) := rfl

theorem colCut_succ (A : U h) (c : Fin h) : colCut A (c.1 + 1) = colEl A c * colCut A c.1 := by
  apply mat_inj
  rw [mat_mul, mat_colEl, Matrix.add_mul, Matrix.one_mul]
  ext i j
  rw [Matrix.add_apply, colCut_apply, colCut_apply, Matrix.mul_apply]
  simp only [Matrix.vecMulVec_apply]
  rw [sum_eq_single c]
  · rw [Pi.single_eq_same, mul_one, colCut_apply]
    by_cases hj : j = c
    · subst hj
      rw [if_pos (by omega), if_neg (lt_irrefl _), if_neg (lt_irrefl _), Matrix.one_apply_eq, mul_one]
      rcases lt_trichotomy i j with hij | hij | hij
      · rw [if_pos hij, Matrix.one_apply_ne hij.ne, zero_add]
      · subst hij
        rw [if_neg (lt_irrefl _), Matrix.one_apply_eq, mat_diag, add_zero]
      · rw [if_neg (not_lt.2 hij.le), Matrix.one_apply_ne hij.ne', mat_lt A hij, add_zero]
    · have h1 : (if j.1 < c.1 then mat A c j else (1 : Matrix (Fin h) (Fin h) F2) c j) = 0 := by
        split_ifs with h2
        · exact mat_lt A (Fin.lt_def.2 h2)
        · exact Matrix.one_apply_ne (Ne.symm hj)
      rw [h1, mul_zero, add_zero]
      have h2 : j.1 ≠ c.1 := fun e => hj (Fin.ext e)
      by_cases h3 : j.1 < c.1
      · rw [if_pos (by omega), if_pos h3]
      · rw [if_neg (by omega), if_neg h3]
  · intro d _ hd
    rw [Pi.single_eq_of_ne hd, mul_zero, zero_mul]
  · exact fun hn => absurd (mem_univ _) hn

/-- **The x_j generate U h.** -/
theorem mem_of_x (H : Subgroup (U h)) (hx : ∀ j, x h j ∈ H) (A : U h) : A ∈ H := by
  classical
  have hS : (subLen H).S = 0 := sum_eq_zero fun j _ => if_pos (hx j)
  have hel : ∀ c : Fin h, colEl A c ∈ H := by
    intro c
    have h1 := Paper.lem_words (subLen H) c.1 (fun i => if i < c then mat A i c else 0) (Pi.single c 1)
      (fun i hi => by
        by_contra hlt
        exact hi (if_neg fun h => hlt h))
      (fun j hj => by
        by_contra hne
        exact hj (Pi.single_eq_of_ne (fun e => hne (by rw [e])) _)) (colEl A c) (mat_colEl A c)
    rw [show ∑ j, (subLen H).val (x h j) = 0 from hS, mul_zero] at h1
    by_contra hn
    have h2 : (subLen H).val (colEl A c) = 1 := if_neg hn
    rw [h2] at h1
    norm_num at h1
  have hcut : ∀ c : ℕ, c ≤ h → colCut A c ∈ H := by
    intro c
    induction c with
    | zero =>
      intro _
      have : colCut A 0 = 1 := by
        apply mat_inj
        ext i j
        rw [colCut_apply, if_neg (Nat.not_lt_zero _), mat_one]
      rw [this]
      exact H.one_mem
    | succ c ih =>
      intro hc
      have h1 := colCut_succ A ⟨c, hc⟩
      simp only at h1
      rw [h1]
      exact H.mul_mem (hel _) (ih (by omega))
  have : colCut A h = A := by
    apply mat_inj
    ext i j
    rw [colCut_apply, if_pos j.2]
  rw [← this]
  exact hcut h le_rfl

/-- Functions that don't change under multiplication by the x_j from the left are constant. -/
theorem const_of_x {β : Type*} (f : U h → β) (hf : ∀ j u, f (x h j * u) = f u) (p q : U h) :
    f p = f q := by
  let H : Subgroup (U h) :=
    { carrier := {g | ∀ u, f (g * u) = f u}
      one_mem' := fun u => by rw [one_mul]
      mul_mem' := fun {a b} ha hb u => by rw [mul_assoc, ha, hb]
      inv_mem' := fun {a} ha u => by rw [← ha, mul_inv_cancel_left] }
  have h1 := mem_of_x H hf (p * q⁻¹) q
  rw [inv_mul_cancel_right] at h1
  exact h1

end Nc.Flag

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# The paper, section "The contracting case: unitriangular groups", from the first estimate on
-/

namespace Paper

open Finset Filter Nc.Flag
open Nc.Tower (U x lo hi)

/-- The constant κ_n of the first estimate. -/
noncomputable def kappa (μ : ℕ) (s : ℝ) (n : ℕ) : ℝ := 18 * Nat.clog 2 n * grow μ s (2 ^ Nat.clog 2 n)

theorem kappa_nonneg (μ : ℕ) {s : ℝ} (hs : 1 ≤ s) (n : ℕ) : 0 ≤ kappa μ s n :=
  mul_nonneg (by positivity) (grow_nonneg μ hs _)

/-- The proof of Lemma lem:first, rank one in the upper right block (Lemma lem:words). -/
theorem lem_first_rank_one {a : ℕ} (l : Len (U (a + a))) (u φ : Fin a → F2) :
    l.val (up (Matrix.vecMulVec u φ)) ≤ 18 * l.S := by
  refine lem_words l a (fun i => if h : i.1 < a then u ⟨i.1, h⟩ else 0)
    (fun i => if h : a ≤ i.1 then φ ⟨i.1 - a, by omega⟩ else 0) (fun i hi => ?_) (fun j hj => ?_) _ ?_
  · by_contra h1
    simp [h1] at hi
  · by_contra h1
    simp [h1] at hj
  · rw [mat_up]
    congr 1
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, wi, Matrix.of_apply, Matrix.transpose_apply,
      Matrix.vecMulVec_apply]
    by_cases h1 : i.1 < a
    · have e1 : ∀ c, i = we (hl (a := a) (b := a)) c ↔ ⟨i.1, h1⟩ = c := by
        intro c
        simp [we, Fin.ext_iff]
      simp only [e1, h1, dif_pos, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, if_true]
      by_cases h2 : a ≤ j.1
      · have e2 : ∀ c, j = we (hr (a := a) (b := a)) c ↔ ⟨j.1 - a, by omega⟩ = c := by
          intro c
          simp only [we, Fin.ext_iff]
          omega
        simp [e2, h2]
      · have e2 : ∀ c, j ≠ we (hr (a := a) (b := a)) c := by
          intro c
          simp only [we, ne_eq, Fin.ext_iff]
          omega
        simp [e2, h2]
    · have e1 : ∀ c, i ≠ we (hl (a := a) (b := a)) c := by
        intro c
        simp only [we, ne_eq, Fin.ext_iff]
        omega
      simp [e1, h1]

/-- The proof of Lemma lem:first: "By Lemmas lem:growth and lem:words the first [the upper right block] contributes at
most 18μ(d+1)s^d ∑_j |x_j|." Here the mean square over the block is bounded, with the sum in place of the mean. -/
theorem lem_first_block {a m : ℕ} {s : ℝ} (l : Len (U (a + a))) (hm : 2 ≤ m) (hs : 1 ≤ s) (hl : Contr l m s) :
    ∑ M : Mt a, l.val (up M) ^ 2 ≤ (Fintype.card (Mt a) : ℝ) * (grow m s a * (18 * l.S)) ^ 2 := by
  have hS := l.S_nonneg
  have h1 : rankMean (fun M : Mt a => l.val (up M)) 1 ≤ (18 * l.S) ^ 2 := by
    rw [rankMean]
    refine div_le_of_le_mul₀ (Nat.cast_nonneg _) (sq_nonneg _) ?_
    rw [mul_comm, ← nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun W hW => pow_le_pow_left₀ (l.nonneg _) ?_ 2
    obtain ⟨p, q, T, rfl⟩ := exists_factor W
    rw [mem_filter, rank_units, rank_dg] at hW
    obtain ⟨i, rfl⟩ := card_eq_one.1 hW.2
    have e : (p : Mt a) * dg {i} * (q : Mt a) =
        Matrix.vecMulVec (fun r => (p : Mt a) r i) (fun c => (q : Mt a) i c) := by
      ext r c
      simp [Matrix.mul_apply, dg, Matrix.diagonal_apply, Matrix.vecMulVec_apply]
    rw [e]
    exact lem_first_rank_one l _ _
  have h2 : ∀ r, r ≤ a → rankMean (fun M : Mt a => l.val (up M)) r ≤ (grow m s a * (18 * l.S)) ^ 2 := by
    intro r hr
    have h := lem_growth l hm hs hl (fun M : Mt a => up M) up_add hr
    rw [← Real.sq_sqrt (rankMean_nonneg _ r)]
    refine pow_le_pow_left₀ (Real.sqrt_nonneg _) (h.trans ?_) 2
    have h3 : √(rankMean (fun M : Mt a => l.val (up M)) 1) ≤ 18 * l.S :=
      (Real.sqrt_le_left (by positivity)).2 h1
    exact mul_le_mul (grow_mono m hs hr) h3 (Real.sqrt_nonneg _) (grow_nonneg m hs a)
  have hmap : ∀ M ∈ (univ : Finset (Mt a)), M.rank ∈ range (a + 1) := fun M _ => by
    rw [mem_range, Nat.lt_succ_iff]
    exact (Matrix.rank_le_card_width M).trans (le_of_eq (Fintype.card_fin a))
  rw [← sum_fiberwise_of_maps_to hmap, ← card_univ, card_eq_sum_card_fiberwise hmap, Nat.cast_sum, Finset.sum_mul]
  refine sum_le_sum fun r hr => ?_
  rcases ((univ : Finset (Mt a)).filter fun M => M.rank = r).eq_empty_or_nonempty with he | he
  · simp [he]
  · have hc : (0 : ℝ) < ((univ : Finset (Mt a)).filter fun M => M.rank = r).card := by exact_mod_cast he.card_pos
    have h := h2 r (Nat.lt_succ_iff.1 (mem_range.1 hr))
    rw [rankMean, div_le_iff₀ hc] at h
    linarith

/-- The proof of Lemma lem:first, the step of the induction: "A uniform element is a product of a uniform element of
the abelian upper right block and uniform elements of the two diagonal blocks", and these "use disjoint sets of
generators". -/
theorem lem_first_double {m : ℕ} {s : ℝ} (hm : 2 ≤ m) (hs : 1 ≤ s) {a : ℕ} {κ : ℝ} (h : Bd m s a κ)
    (hκ : 0 ≤ κ) : Bd m s (a + a) (18 * grow m s a + κ) := by
  intro l hC
  set A := l.comap (win (hl (a := a) (b := a))) with hA
  set B := l.comap (win (hr (a := a) (b := a))) with hB
  have hAr : A.rms ≤ κ * A.S := h A (hC.comap _)
  have hBr : B.rms ≤ κ * B.S := h B (hC.comap _)
  have hS := S_add_le l
  rw [← hA, ← hB] at hS
  have hS0 := l.S_nonneg
  have hM := lem_first_block l hm hs hC (a := a)
  set cM : ℝ := (Fintype.card (Matrix (Fin a) (Fin a) F2) : ℝ) with hcM
  set cU : ℝ := (Fintype.card (U a) : ℝ) with hcU
  have hcM0 : 0 < cM := by rw [hcM]; exact_mod_cast Fintype.card_pos
  have hcU0 : 0 < cU := by rw [hcU]; exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card (U (a + a)) : ℝ) = cU * (cM * cU) := by
    have := Fintype.card_of_bijective (blk_bijective (a := a) (b := a))
    rw [← this, Fintype.card_prod, Fintype.card_prod]
    push_cast
    rfl
  have hsum : ∀ f : U (a + a) → ℝ, ∑ g, f g = ∑ t, f (blk t) := fun f =>
    (Function.Bijective.sum_comp blk_bijective f).symm
  have key : √(∑ g : U (a + a), l.val g ^ 2) ≤
      √(∑ t : U a × Matrix (Fin a) (Fin a) F2 × U a, B.val t.2.2 ^ 2) +
      (√(∑ t : U a × Matrix (Fin a) (Fin a) F2 × U a, l.val (up t.2.1) ^ 2) +
      √(∑ t : U a × Matrix (Fin a) (Fin a) F2 × U a, A.val t.1 ^ 2)) := by
    rw [hsum]
    refine three_le (fun t => l.val (blk t)) (fun t => B.val t.2.2) (fun t => l.val (up t.2.1))
      (fun t => A.val t.1) (fun _ => l.nonneg _) (fun _ => B.nonneg _) (fun _ => l.nonneg _)
      (fun _ => A.nonneg _) fun t => ?_
    have h1 := l.mul' (win hr t.2.2 * up t.2.1) (win hl t.1)
    have h2 := l.mul' (win hr t.2.2) (up t.2.1)
    have h3 : B.val t.2.2 = l.val (win hr t.2.2) := rfl
    have h4 : A.val t.1 = l.val (win hl t.1) := rfl
    rw [h3, h4]
    exact h1.trans (by linarith)
  have s1 : ∑ t : U a × Matrix (Fin a) (Fin a) F2 × U a, B.val t.2.2 ^ 2 =
      cU * (cM * cU) * B.rms ^ 2 := by
    rw [Len.rms_sq, Fintype.sum_prod_type, ← hcU]
    simp only [Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul, ← hcU, ← hcM]
    field_simp
  have s2 : ∑ t : U a × Matrix (Fin a) (Fin a) F2 × U a, l.val (up t.2.1) ^ 2 ≤
      cU * (cM * cU) * (grow m s a * (18 * l.S)) ^ 2 := by
    simp only [Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul, ← hcU, ← mul_sum]
    calc _ ≤ cU * (cU * (cM * (grow m s a * (18 * l.S)) ^ 2)) := by gcongr
      _ = _ := by ring
  have s3 : ∑ t : U a × Matrix (Fin a) (Fin a) F2 × U a, A.val t.1 ^ 2 =
      cU * (cM * cU) * A.rms ^ 2 := by
    rw [Len.rms_sq, Fintype.sum_prod_type, ← hcU]
    simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul, ← hcU, ← hcM,
      ← mul_sum]
    field_simp
  have hc0 : 0 ≤ cU * (cM * cU) := by positivity
  have hg0 := grow_nonneg m hs a
  have t2 : √(∑ t : U a × Matrix (Fin a) (Fin a) F2 × U a, l.val (up t.2.1) ^ 2) ≤
      √(cU * (cM * cU)) * (grow m s a * (18 * l.S)) := by
    refine (Real.sqrt_le_sqrt s2).trans (le_of_eq ?_)
    rw [Real.sqrt_mul hc0, Real.sqrt_sq (by positivity)]
  rw [s1, s3, Real.sqrt_mul hc0, Real.sqrt_mul hc0, Real.sqrt_sq A.rms_nonneg,
    Real.sqrt_sq B.rms_nonneg] at key
  have hsq : 0 < √(cU * (cM * cU)) := Real.sqrt_pos.2 (by positivity)
  have hr : l.rms = √(∑ g : U (a + a), l.val g ^ 2) / √(cU * (cM * cU)) := by
    rw [Len.rms, hcard, Real.sqrt_div' _ hc0]
  rw [hr, div_le_iff₀ hsq]
  have hκS : κ * A.S + κ * B.S ≤ κ * l.S := by rw [← mul_add]; exact mul_le_mul_of_nonneg_left hS hκ
  calc √(∑ g : U (a + a), l.val g ^ 2)
      ≤ √(cU * (cM * cU)) * B.rms + (√(cU * (cM * cU)) * (grow m s a * (18 * l.S)) +
        √(cU * (cM * cU)) * A.rms) := key.trans (add_le_add le_rfl (add_le_add t2 le_rfl))
    _ = √(cU * (cM * cU)) * (B.rms + grow m s a * (18 * l.S) + A.rms) := by ring
    _ ≤ √(cU * (cM * cU)) * ((18 * grow m s a + κ) * l.S) := by
        apply mul_le_mul_of_nonneg_left _ hsq.le
        linarith
    _ = _ := by ring

/-- κ_n² n = o(n²). -/
theorem kappa_small {μ : ℕ} {s : ℝ} (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) :
    Tendsto (fun n : ℕ => kappa μ s n ^ 2 * n / (n : ℝ) ^ 2) atTop (nhds 0) := by
  have hm0 : (0 : ℝ) < μ := by exact_mod_cast (by omega : 0 < μ)
  set ρ : ℝ := s ^ 2 / μ with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hm0]; exact hsm
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L₀, hL₀⟩ := exists_log_large hρ0 hρ1 (show (0 : ℝ) < ε / (2 * (324 * 2 * (μ : ℝ) ^ 4)) by positivity)
  refine ⟨μ ^ L₀ + 2, fun n hn => ?_⟩
  set i := Nat.clog 2 n with hi
  set L := Nat.log μ (2 ^ i) with hL
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hni : n ≤ 2 ^ i := Nat.le_pow_clog one_lt_two n
  have hi2 : 2 ^ i ≤ 2 * n := by
    obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by have := Nat.clog_pos one_lt_two (show 2 ≤ n by omega); omega⟩
    have h : 2 ^ i.pred < n := Nat.pow_pred_clog_lt_self one_lt_two (by omega)
    rw [hj, Nat.pred_succ] at h
    rw [hj, pow_succ]
    omega
  have hLL : L₀ ≤ L := Nat.le_log_of_pow_le (by omega) (by omega)
  have hiL : (i : ℝ) ≤ μ * ((L : ℝ) + 1) := by
    have h1 : 2 ^ i < 2 ^ (μ * (L + 1)) := by
      calc 2 ^ i < μ ^ (L + 1) := Nat.lt_pow_succ_log_self (by omega) _
        _ ≤ (2 ^ μ) ^ (L + 1) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
        _ = 2 ^ (μ * (L + 1)) := by rw [← pow_mul]
    have h2 : i < μ * (L + 1) := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
    exact_mod_cast h2.le
  have hmL : (μ : ℝ) ^ L ≤ 2 * n := by
    exact_mod_cast (Nat.pow_log_le_self μ (Nat.two_pow_pos i).ne').trans hi2
  have e0 : (s ^ L) ^ 2 = ρ ^ L * (μ : ℝ) ^ L := by
    rw [← mul_pow, hρ, div_mul_cancel₀ _ hm0.ne', ← pow_mul, ← pow_mul, mul_comm]
  have h5 : kappa μ s n ^ 2 ≤ 324 * 2 * (μ : ℝ) ^ 4 * (((L : ℝ) + 1) ^ 4 * ρ ^ L) * n := by
    have e : kappa μ s n ^ 2 = 324 * (i : ℝ) ^ 2 * ((μ : ℝ) ^ 2 * ((L : ℝ) + 1) ^ 2 * (ρ ^ L * (μ : ℝ) ^ L)) := by
      rw [kappa, grow, ← hi, ← hL, ← e0]
      ring
    rw [e]
    calc _ ≤ 324 * ((μ : ℝ) * ((L : ℝ) + 1)) ^ 2 * ((μ : ℝ) ^ 2 * ((L : ℝ) + 1) ^ 2 * (ρ ^ L * (2 * n))) := by
          gcongr
      _ = _ := by ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ (by positivity)]
  calc kappa μ s n ^ 2 * n ≤ 324 * 2 * (μ : ℝ) ^ 4 * (ε / (2 * (324 * 2 * (μ : ℝ) ^ 4))) * n * n := by
        gcongr
        refine h5.trans ?_
        gcongr
        exact hL₀ L hLL
    _ = ε / 2 * (n : ℝ) ^ 2 := by field_simp
    _ < ε * (n : ℝ) ^ 2 := by
        have : 0 < ε * (n : ℝ) ^ 2 := by positivity
        linarith

/-- **Paper: Lemma lem:first.** "There are κ_n with κ_n² n = o(n²) such that every contracting length on U_n satisfies
(E_g|g|²)^(1/2) ≤ κ_n ∑_j|x_j|." Here κ_n is the explicit kappa μ s n. -/
theorem lem_first {μ : ℕ} {s : ℝ} (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) :
    Tendsto (fun n : ℕ => kappa μ s n ^ 2 * n / (n : ℝ) ^ 2) atTop (nhds 0) ∧
      ∀ (n : ℕ) (l : Len (U n)), Contr l μ s →
        √((∑ g : U n, l.val g ^ 2) / Fintype.card (U n)) ≤ kappa μ s n * ∑ j : Fin (n - 1), l.val (x n j) := by
  refine ⟨kappa_small hμ hs hsm, fun n => ?_⟩
  have hpow : ∀ i : ℕ, Bd μ s (2 ^ i) (18 * i * grow μ s (2 ^ i)) := by
    intro i
    induction i with
    | zero => simpa using bd_one μ s
    | succ i ih =>
      have h := lem_first_double hμ hs ih (by have := grow_nonneg μ hs (2 ^ i); positivity)
      rw [← two_mul, ← pow_succ'] at h
      intro l hl
      refine (h l hl).trans (mul_le_mul_of_nonneg_right ?_ l.S_nonneg)
      have h1 := grow_mono μ hs (Nat.pow_le_pow_right (n := 2) (by norm_num) (Nat.le_succ i))
      have : 18 * (i : ℝ) * grow μ s (2 ^ i) ≤ 18 * i * grow μ s (2 ^ (i + 1)) := by gcongr
      push_cast
      linarith
  exact bd_mono (Nat.le_pow_clog one_lt_two n) (kappa_nonneg μ hs n) (hpow _)

/-- C(n) = κ_n² n. -/
noncomputable def windowConst (μ : ℕ) (s : ℝ) (n : ℕ) : ℝ := kappa μ s n ^ 2 * n

theorem windowConst_nonneg (μ : ℕ) (s : ℝ) (n : ℕ) : 0 ≤ windowConst μ s n :=
  mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-! ### Windows -/

section Fixed

variable {G Z : Type} [Group G] [MetricSpace Z] [Cat.CN Z]

open Cat in
/-- A point of a segment between fixed points is fixed: the point in Lemma lem:toolkit(a) is the only one with these
distances. -/
theorem segment_fixed (A : IsoAct G Z) {x v q : Z} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (hx : A.Fix x) (hv : A.Fix v)
    (e1 : dist x q = t * dist x v) (e2 : dist q v = (1 - t) * dist x v) : A.Fix q := by
  intro g
  obtain ⟨γ, -, huniq, -⟩ := (lem_toolkit (Y := Z)).1 x v t h0 h1
  rw [huniq q e1 e2]
  refine huniq _ ?_ ?_
  · rw [← huniq q e1 e2]
    conv_lhs => rw [← hx g]
    rw [A.iso', e1]
  · rw [← huniq q e1 e2]
    conv_lhs => rw [← hv g]
    rw [A.iso', e2]

variable [Fintype G]

/-- "These form a closed convex set, which contains the barycenter of every orbit." In the project P z is that
barycenter; projection_var shows that it is the nearest point. -/
theorem fixed_closed_convex (A : IsoAct G Z) :
    IsClosed {y : Z | A.Fix y} ∧
      (∀ x, A.Fix x → ∀ v, A.Fix v → ∀ q, dist x q = dist x v / 2 → dist q v = dist x v / 2 → A.Fix q) ∧
      ∀ z, A.Fix (A.P z) := by
  refine ⟨?_, fun x hx v hv q e1 e2 => segment_fixed A (t := 1 / 2) (by norm_num) (by norm_num) hx hv
    (by rw [e1]; ring) (by rw [e2]; ring), A.P_fix⟩
  have : {y : Z | A.Fix y} = ⋂ g, {y | A.act g y = y} := Set.ofPred_forall _
  rw [this]
  exact isClosed_iInter fun g => isClosed_eq (A.isometry g).continuous continuous_id

/-- Lemma lem:toolkit(d) for the fixed set: |z Pz|² + |Pz q|² ≤ |zq|² for every fixed q. -/
theorem projection_var (A : IsoAct G Z) {q : Z} (hq : A.Fix q) (z : Z) :
    dist z (A.P z) ^ 2 + dist (A.P z) q ^ 2 ≤ dist z q ^ 2 := by
  obtain ⟨hcl, hconv, hP⟩ := fixed_closed_convex A
  obtain ⟨P₀, hP₀, -, hvar⟩ := (lem_toolkit (Y := Z)).2.2.2.1 {y | A.Fix y} hcl ⟨_, hP z⟩ hconv z
  have h1 := hvar _ (hP z)
  have h2 := A.P_spec z P₀
  have e1 : ∀ g, dist (A.P z) (A.act g z) = dist z (A.P z) := fun g => by
    conv_lhs => rw [← A.P_fix z g]
    rw [A.iso', dist_comm]
  have e2 : ∀ g, dist P₀ (A.act g z) = dist z P₀ := fun g => by
    conv_lhs => rw [← hP₀ g]
    rw [A.iso', dist_comm]
  simp only [e1, e2, one_mul, sum_const, card_univ, nsmul_eq_mul, mul_one, ← mul_add] at h2
  have h3 := le_of_mul_le_mul_left h2 (by exact_mod_cast Fintype.card_pos)
  have h4 : dist P₀ (A.P z) ^ 2 ≤ 0 := by linarith [sq_nonneg (dist P₀ (A.P z))]
  rw [← dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h4 (sq_nonneg _)))]
  exact hvar q hq

/-- The P of the windows is the nearest-point projection to the fixed set: P z is fixed, is at least as near to z as every
fixed point, and is the only fixed point with this property. -/
theorem projection_nearest [DecidableEq G] (A : IsoAct G Z) (z : Z) :
    A.Fix (A.P z) ∧ (∀ y, A.Fix y → dist z (A.P z) ≤ dist z y) ∧
      ∀ y, A.Fix y → dist z y ≤ dist z (A.P z) → y = A.P z := by
  refine ⟨A.P_fix z, fun y hy => ?_, fun y hy h => ?_⟩
  · refine (abs_le_of_sq_le_sq' (show dist z (A.P z) ^ 2 ≤ dist z y ^ 2 from ?_) dist_nonneg).2
    linarith [projection_var A hy z, sq_nonneg (dist (A.P z) y)]
  · have h1 := projection_var A hy z
    have h2 : dist z y ^ 2 ≤ dist z (A.P z) ^ 2 := pow_le_pow_left₀ dist_nonneg h 2
    have h3 : dist (A.P z) y ^ 2 ≤ 0 := by linarith
    exact (dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _)))).symm

/-- "So |z Pz|² ≤ E_g|z,gz|²." -/
theorem projection_sq_le (A : IsoAct G Z) (z : Z) :
    dist z (A.P z) ^ 2 ≤ (∑ g : G, dist z (A.act g z) ^ 2) / Fintype.card G := by
  have h := A.P_spec z z
  simp only [one_mul, sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  rw [le_div_iff₀ (by exact_mod_cast Fintype.card_pos)]
  linarith [show 0 ≤ ∑ g : G, dist (A.P z) (A.act g z) ^ 2 from sum_nonneg fun _ _ => sq_nonneg _]

/-- "q projects to v": a point between v = Pa and a has the projection v. -/
theorem projection_segment [DecidableEq G] (A : IsoAct G Z) {a q : Z} {σ : ℝ}
    (e1 : dist (A.P a) q = σ * dist (A.P a) a) (e2 : dist q a = (1 - σ) * dist (A.P a) a) : A.P q = A.P a := by
  refine (projection_nearest A a).2.2 _ (A.P_fix q) ?_
  have h1 := dist_triangle a q (A.P q)
  have h2 := (projection_nearest A q).2.1 _ (A.P_fix a)
  rw [dist_comm a q] at h1
  rw [dist_comm q (A.P a)] at h2
  rw [dist_comm a (A.P a)]
  linarith

end Fixed

section Windows

variable {μ : ℕ} {s : ℝ} {h : ℕ} {Z : Type} [MetricSpace Z] [Cat.CN Z] (A : IsoAct (U h) Z)

/-- "For disjoint windows the projection of one maps the fixed set of the other into itself, as the two groups
commute." -/
theorem windows_commute {p n p' n' : ℕ} (hd : p + n ≤ p') (hp' : p' + n' ≤ h) :
    (∀ z, (A.W p n).Fix z → (A.W p n).Fix ((A.W p' n').P z)) ∧
      ∀ z, (A.W p' n').Fix z → (A.W p' n').Fix ((A.W p n).P z) := by
  refine ⟨fun z hz a => ?_, fun z hz b => ?_⟩
  · have h1 := (A.W p' n').P_comm (A.act (wh h p n a)) (A.isometry _) (A.surj _)
      (fun b z => by
        show A.act _ (A.act (wh h p' n' b) z) = A.act (wh h p' n' b) (A.act _ z)
        rw [← A.mul', ← A.mul', IsoAct.wh_comm hd hp']) z
    show A.act (wh h p n a) _ = _
    rw [h1, show A.act (wh h p n a) z = z from hz a]
  · have h1 := (A.W p n).P_comm (A.act (wh h p' n' b)) (A.isometry _) (A.surj _)
      (fun a z => by
        show A.act _ (A.act (wh h p n a) z) = A.act (wh h p n a) (A.act _ z)
        rw [← A.mul', ← A.mul', IsoAct.wh_comm hd hp']) z
    show A.act (wh h p' n' b) _ = _
    rw [h1, show A.act (wh h p' n' b) z = z from hz b]

/-- The inequality (eq:window) of the paper: |z Pz|² ≤ C(n) ∑ e_j(z)² over the generators of the window. "By Lemma
lem:first and the Cauchy–Schwarz inequality." -/
theorem eq_window (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) (hA : ∀ z, Contr (A.len z) μ s) {n p : ℕ}
    (hp : p + n ≤ h) (z : Z) :
    dist z ((A.W p n).P z) ^ 2 ≤ windowConst μ s n * ∑ j ∈ Ico p (p + n - 1), A.e j z ^ 2 := by
  have hC : Contr ((A.W p n).len z) μ s := (hA z).comap (wh h p n)
  have h1 : ((A.W p n).len z).rms ≤ kappa μ s n * ((A.W p n).len z).S := (lem_first hμ hs hsm).2 n _ hC
  have h2 := projection_sq_le (A.W p n) z
  have h3 : (∑ g : U n, dist z ((A.W p n).act g z) ^ 2) / Fintype.card (U n) = ((A.W p n).len z).rms ^ 2 := by
    rw [Len.rms_sq]
    simp only [IsoAct.len_val]
  rw [h3] at h2
  have h4 : ((A.W p n).len z).rms ^ 2 ≤ (kappa μ s n * ((A.W p n).len z).S) ^ 2 :=
    pow_le_pow_left₀ (Len.rms_nonneg _) h1 2
  have h5 : ((A.W p n).len z).S = ∑ j : Fin (n - 1), A.e (p + j.1) z := by
    unfold Len.S
    refine sum_congr rfl fun j _ => ?_
    have hj : p + j.1 < h - 1 := by have := j.2; omega
    have e1 : wh h p n (x n j) = x h ⟨p + j.1, hj⟩ := by rw [wh_eq hp, win_x]; rfl
    have e2 : ((A.W p n).len z).val (x n j) = dist z (A.act (wh h p n (x n j)) z) := rfl
    rw [e2, e1]
    unfold IsoAct.e
    rw [dif_pos hj]
  have h6 : (((A.W p n).len z).S) ^ 2 ≤ n * ∑ j ∈ Ico p (p + n - 1), A.e j z ^ 2 := by
    have h7 : ∑ j ∈ Ico p (p + n - 1), A.e j z ^ 2 = ∑ j : Fin (n - 1), A.e (p + j.1) z ^ 2 := by
      rw [sum_Ico_eq_sum_range, ← Fin.sum_univ_eq_sum_range (fun j => A.e (p + j) z ^ 2)]
      rw [show p + n - 1 - p = n - 1 by omega]
    rw [h5, h7]
    have h8 := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun j : Fin (n - 1) => A.e (p + j.1) z)
    rw [card_univ, Fintype.card_fin] at h8
    refine h8.trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => sq_nonneg _))
    exact_mod_cast Nat.sub_le n 1
  calc _ ≤ kappa μ s n ^ 2 * (((A.W p n).len z).S) ^ 2 := by rw [← mul_pow]; exact h2.trans h4
    _ ≤ kappa μ s n ^ 2 * (n * ∑ j ∈ Ico p (p + n - 1), A.e j z ^ 2) := mul_le_mul_of_nonneg_left h6 (sq_nonneg _)
    _ = _ := by rw [windowConst]; ring

/-- The proof of Lemma lem:tele: "By Lemma lem:toolkit(c) each generator moves the barycenter by at most 1/n times
the sum of what it moves the n points." -/
theorem lem_tele_generator {n : ℕ} {y : Fin n → Z} {b : Z}
    (hb : ∀ w, (n : ℝ) * dist w b ^ 2 + ∑ i, dist b (y i) ^ 2 ≤ ∑ i, dist w (y i) ^ 2) (j : ℕ) :
    (n : ℝ) * A.e j b ≤ ∑ i, A.e j (y i) := by
  unfold IsoAct.e
  split_ifs with hj
  · refine (lem_toolkit (Y := Z)).2.2.1.2 n y (fun i => A.act (x h ⟨j, hj⟩) (y i)) b (A.act (x h ⟨j, hj⟩) b) hb
      fun w => ?_
    obtain ⟨w, rfl⟩ := A.surj (x h ⟨j, hj⟩) w
    simp only [A.iso']
    exact hb w
  · simp

/-- **Paper: Lemma lem:tele.** "Let u ≥ 2, p+3u ≤ h, ζ ≥ 0 and 4C(3u) ≤ ζ²(u−1)². If a is fixed by [p,p+2u), then
|a, P_{[p+u,p+3u)}a| ≥ (1−ζ)R, where R = |a, P_{[p,p+3u)}a|." -/
theorem lem_tele (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) (hA : ∀ z, Contr (A.len z) μ s) {u p : ℕ} {ζ : ℝ}
    (hu : 2 ≤ u) (hp : p + 3 * u ≤ h) (hζ : 0 ≤ ζ)
    (hC : 4 * windowConst μ s (3 * u) ≤ ζ ^ 2 * ((u : ℝ) - 1) ^ 2) {a : Z} (ha : (A.W p (2 * u)).Fix a) :
    (1 - ζ) * dist a ((A.W p (3 * u)).P a) ≤ dist a ((A.W (p + u) (2 * u)).P a) := by
  set R := dist a ((A.W p (3 * u)).P a) with hR
  set B : ℕ → Z := fun k => (A.W (p + k) (3 * u - k)).P a with hB
  have hBfix : ∀ k, (A.W (p + k) (3 * u - k)).Fix (B k) := fun k => IsoAct.P_fix _ a
  have hBu : B u = (A.W (p + u) (2 * u)).P a := by
    show (A.W (p + u) (3 * u - u)).P a = _
    rw [show 3 * u - u = 2 * u by omega]
  have hu1 : (0 : ℝ) < (u : ℝ) - 1 := by
    have : (2 : ℝ) ≤ u := by exact_mod_cast hu
    linarith
  -- Lemma lem:toolkit (d)
  have hstep : ∀ k, k < 3 * u → dist (B k) (B (k + 1)) ^ 2 ≤ dist a (B k) ^ 2 - dist a (B (k + 1)) ^ 2 := by
    intro k hk
    have h1 := projection_var (A.W (p + (k + 1)) (3 * u - (k + 1)))
      ((hBfix k).sub A (by omega) (by omega) (by omega)) a
    rw [dist_comm ((A.W (p + (k + 1)) (3 * u - (k + 1))).P a) (B k)] at h1
    show dist (B k) ((A.W (p + (k + 1)) (3 * u - (k + 1))).P a) ^ 2 ≤
      dist a (B k) ^ 2 - dist a ((A.W (p + (k + 1)) (3 * u - (k + 1))).P a) ^ 2
    linarith
  have hφR : dist a (B u) ≤ R :=
    (projection_nearest (A.W (p + u) (3 * u - u)) a).2.1 _
      (((A.W p (3 * u)).P_fix a).sub A (by omega) (by omega) hp)
  have hφ : ∀ k, u ≤ k → k ≤ 3 * u → dist a (B k) ≤ dist a (B u) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ k hk ih =>
      intro hk3
      refine le_trans ?_ (ih (by omega))
      exact (abs_le_of_sq_le_sq' (show dist a (B (k + 1)) ^ 2 ≤ dist a (B k) ^ 2 by
        linarith [hstep k (by omega), sq_nonneg (dist (B k) (B (k + 1)))]) dist_nonneg).2
  -- the barycenter of the u-1 points
  obtain ⟨b, hb⟩ := (lem_toolkit (Y := Z)).2.2.1.1 (u - 1) (fun i => B (u + 1 + i.1)) (by omega)
  have hw : ((u - 1 : ℕ) : ℝ) = (u : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ u), Nat.cast_one]
  have hab : dist a b ≤ dist a (B u) := by
    refine (abs_le_of_sq_le_sq' (show dist a b ^ 2 ≤ dist a (B u) ^ 2 from ?_) dist_nonneg).2
    have h1 := hb a
    have h2 : ∑ i : Fin (u - 1), dist a (B (u + 1 + i.1)) ^ 2 ≤ ((u : ℝ) - 1) * dist a (B u) ^ 2 := by
      have : ((u : ℝ) - 1) * dist a (B u) ^ 2 = ∑ _i : Fin (u - 1), dist a (B u) ^ 2 := by simp [hw]
      rw [this]
      refine sum_le_sum fun i _ => pow_le_pow_left₀ dist_nonneg ?_ 2
      exact hφ _ (by omega) (by have := i.2; omega)
    rw [hw] at h1
    have h3 : 0 ≤ ∑ i : Fin (u - 1), dist b (B (u + 1 + i.1)) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    exact le_of_mul_le_mul_left (by linarith) hu1
  -- for u < k < 2u all generators of the window fix b_k, apart from one
  have he : ∀ t, t < 3 * u - 1 → ∀ k, u + 1 ≤ k → k < 2 * u → k ≠ t + 1 → A.e (p + t) (B k) = 0 := by
    intro t ht k hk1 hk2 hkt
    by_cases htk : k ≤ t
    · exact A.e_zero (hBfix k) (by omega) (by omega) (by omega)
    · have h1 : (A.W (p + t) 2).Fix a := ha.sub A (by omega) (by omega) (by omega)
      exact A.e_zero ((windows_commute A (by omega) (by omega)).1 a h1) le_rfl le_rfl (by omega)
  have he2 : ∀ t, u ≤ t → t + 1 < 2 * u → A.e (p + t) (B (t + 1)) ≤ 2 * dist (B t) (B (t + 1)) := by
    intro t h1 h2
    rw [dist_comm]
    exact A.e_le (hBfix t) (by omega) (by omega) (by omega) _
  have hde : ∀ t, t < 3 * u - 1 → (((u : ℝ) - 1) * A.e (p + t) b) ^ 2 ≤
      if u ≤ t ∧ t + 1 < 2 * u then 4 * (dist a (B t) ^ 2 - dist a (B (t + 1)) ^ 2) else 0 := by
    intro t ht
    have h1 := lem_tele_generator A hb (p + t)
    rw [hw] at h1
    have h0 : 0 ≤ ((u : ℝ) - 1) * A.e (p + t) b := mul_nonneg hu1.le (A.e_nonneg _ _)
    split_ifs with hc
    · have h2 : ∑ i : Fin (u - 1), A.e (p + t) (B (u + 1 + i.1)) = A.e (p + t) (B (t + 1)) := by
        rw [sum_eq_single (⟨t - u, by omega⟩ : Fin (u - 1))]
        · congr 2
          simp only
          omega
        · intro i _ hi
          have := i.2
          refine he t ht _ (by omega) (by omega) ?_
          intro h3
          apply hi
          apply Fin.ext
          simp only
          omega
        · intro h3
          exact absurd (mem_univ _) h3
      rw [h2] at h1
      calc (((u : ℝ) - 1) * A.e (p + t) b) ^ 2 ≤ (2 * dist (B t) (B (t + 1))) ^ 2 :=
            pow_le_pow_left₀ h0 (h1.trans (he2 t hc.1 hc.2)) 2
        _ = 4 * dist (B t) (B (t + 1)) ^ 2 := by ring
        _ ≤ _ := by
          have := hstep t (by omega)
          linarith
    · have h2 : ∑ i : Fin (u - 1), A.e (p + t) (B (u + 1 + i.1)) = 0 := by
        refine sum_eq_zero fun i _ => ?_
        have := i.2
        refine he t ht _ (by omega) (by omega) ?_
        intro h3
        exact hc ⟨by omega, by omega⟩
      rw [h2] at h1
      rw [le_antisymm h1 h0]
      norm_num
  have hsum : ((u : ℝ) - 1) ^ 2 * ∑ j ∈ Ico p (p + 3 * u - 1), A.e j b ^ 2 ≤ 4 * R ^ 2 := by
    have h1 : ∑ j ∈ Ico p (p + 3 * u - 1), A.e j b ^ 2 = ∑ t ∈ range (3 * u - 1), A.e (p + t) b ^ 2 := by
      rw [sum_Ico_eq_sum_range, show p + 3 * u - 1 - p = 3 * u - 1 by omega]
    rw [h1, mul_sum]
    have h2 : ∀ t ∈ range (3 * u - 1), ((u : ℝ) - 1) ^ 2 * A.e (p + t) b ^ 2 ≤
        if u ≤ t ∧ t + 1 < 2 * u then 4 * (dist a (B t) ^ 2 - dist a (B (t + 1)) ^ 2) else 0 := by
      intro t ht
      rw [← mul_pow]
      exact hde t (mem_range.1 ht)
    refine (sum_le_sum h2).trans ?_
    rw [← sum_filter]
    have h3 : (range (3 * u - 1)).filter (fun t => u ≤ t ∧ t + 1 < 2 * u) = Ico u (2 * u - 1) := by
      ext t
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    rw [h3, ← mul_sum]
    have h4 : ∀ m, u ≤ m → ∑ t ∈ Ico u m, (dist a (B t) ^ 2 - dist a (B (t + 1)) ^ 2) =
        dist a (B u) ^ 2 - dist a (B m) ^ 2 := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ m hm ih => rw [sum_Ico_succ_top hm, ih]; ring
    rw [h4 _ (by omega)]
    have := sq_nonneg (dist a (B (2 * u - 1)))
    have := pow_le_pow_left₀ dist_nonneg hφR 2
    linarith
  -- by (eq:window) b is within ζR of a fixed point of the window
  have hR0 : 0 ≤ R := dist_nonneg
  have hbP : dist b ((A.W p (3 * u)).P b) ≤ ζ * R := by
    refine (abs_le_of_sq_le_sq' (show dist b ((A.W p (3 * u)).P b) ^ 2 ≤ (ζ * R) ^ 2 from ?_)
      (mul_nonneg hζ hR0)).2
    have h2 : ((u : ℝ) - 1) ^ 2 * dist b ((A.W p (3 * u)).P b) ^ 2 ≤ ((u : ℝ) - 1) ^ 2 * (ζ * R) ^ 2 := by
      calc _ ≤ ((u : ℝ) - 1) ^ 2 * (windowConst μ s (3 * u) * ∑ j ∈ Ico p (p + 3 * u - 1), A.e j b ^ 2) :=
            mul_le_mul_of_nonneg_left (eq_window A hμ hs hsm hA hp b) (sq_nonneg _)
        _ = windowConst μ s (3 * u) * (((u : ℝ) - 1) ^ 2 * ∑ j ∈ Ico p (p + 3 * u - 1), A.e j b ^ 2) := by ring
        _ ≤ windowConst μ s (3 * u) * (4 * R ^ 2) := mul_le_mul_of_nonneg_left hsum (windowConst_nonneg μ s _)
        _ = 4 * windowConst μ s (3 * u) * R ^ 2 := by ring
        _ ≤ ζ ^ 2 * ((u : ℝ) - 1) ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_right hC (sq_nonneg _)
        _ = _ := by ring
    exact le_of_mul_le_mul_left h2 (by positivity)
  have h1 := (projection_nearest (A.W p (3 * u)) a).2.1 _ ((A.W p (3 * u)).P_fix b)
  rw [← hR] at h1
  have h2 := dist_triangle a b ((A.W p (3 * u)).P b)
  rw [← hBu]
  linarith

end Windows

open Cat in
/-- The proof of Lemma lem:angle for any two fixed sets with a common point v. If every point q that divides [v,a], a the
first projection of z, is at squared distance at least (1−c²)|qv|² from the second fixed set, then
|aa′|² ≤ |za|² + |za′|² + 2c|za||za′|. -/
theorem lem_angle_projections {G₁ G₂ Z : Type} [Group G₁] [Fintype G₁] [DecidableEq G₁] [Group G₂] [Fintype G₂]
    [DecidableEq G₂] [MetricSpace Z] [CN Z] (A₁ : IsoAct G₁ Z) (A₂ : IsoAct G₂ Z) {c : ℝ} (hc : 0 < c) (z v : Z)
    (hv1 : A₁.Fix v) (hv2 : A₂.Fix v)
    (hq : ∀ (q : Z) (σ : ℝ), 0 < σ → σ ≤ 1 → dist v q = σ * dist v (A₁.P z) →
      dist q (A₁.P z) = (1 - σ) * dist v (A₁.P z) → (1 - c ^ 2) * dist v q ^ 2 ≤ dist q (A₂.P q) ^ 2) :
    dist (A₁.P z) (A₂.P z) ^ 2 ≤
      dist z (A₁.P z) ^ 2 + dist z (A₂.P z) ^ 2 + 2 * c * (dist z (A₁.P z) * dist z (A₂.P z)) := by
  set a := A₁.P z with ha
  set a' := A₂.P z with ha'
  have hA1 := projection_var A₁ hv1 z
  have hA2 := projection_var A₂ hv2 z
  rw [← ha] at hA1
  rw [← ha'] at hA2
  rcases (dist_nonneg (x := z) (y := a)).eq_or_lt with h0 | hr
  · rw [← h0, ← dist_eq_zero.1 h0.symm]
    simp
  rcases (dist_nonneg (x := z) (y := a')).eq_or_lt with h0 | hr'
  · rw [← h0, ← dist_eq_zero.1 h0.symm, dist_comm a z]
    simp
  have hpos : 0 ≤ 2 * c * (dist z a * dist z a') := by positivity
  rcases (dist_nonneg (x := v) (y := a)).eq_or_lt with h0 | hα
  · rw [dist_eq_zero.1 h0.symm, dist_comm a' a] at hA2
    linarith [sq_nonneg (dist z a')]
  rcases (dist_nonneg (x := v) (y := a')).eq_or_lt with h0 | hβ
  · rw [dist_eq_zero.1 h0.symm] at hA1
    linarith [sq_nonneg (dist z a)]
  rw [dist_comm a v] at hA1
  rw [dist_comm a' v] at hA2
  -- q, q′ divide [v,a], [v,a′] in ratios σ, τ with τβ = cσα
  set α := dist v a with hαd
  set β := dist v a' with hβd
  have hQ : α ^ 2 + β ^ 2 - 2 * c * (α * β) ≤ dist a a' ^ 2 := by
    set N := β + c * α with hN
    have hN0 : 0 < N := by positivity
    set σ := β / N with hσ
    set τ := c * α / N with hτ
    have hσ0 : 0 < σ := by positivity
    have hτ0 : 0 < τ := by positivity
    have hσ1 : σ ≤ 1 := by
      rw [hσ, div_le_one hN0, hN]
      linarith [mul_nonneg hc.le hα.le]
    have hτ1 : τ ≤ 1 := by
      rw [hτ, div_le_one hN0, hN]
      linarith
    obtain ⟨q, ⟨q1, q2⟩, -, q3⟩ := (lem_toolkit (Y := Z)).1 v a σ hσ0.le hσ1
    obtain ⟨q', ⟨p1, p2⟩, -, p3⟩ := (lem_toolkit (Y := Z)).1 v a' τ hτ0.le hτ1
    have h2 := hq q σ hσ0 hσ1 q1 q2
    have f2 : A₂.Fix q' := segment_fixed A₂ hτ0.le hτ1 hv2 (A₂.P_fix z) p1 p2
    have h4 : dist q (A₂.P q) ^ 2 ≤ dist q q' ^ 2 :=
      pow_le_pow_left₀ dist_nonneg ((projection_nearest A₂ q).2.1 _ f2) 2
    have h5 := p3 q
    have h6 := q3 a'
    rw [dist_comm a' q, dist_comm a' v, dist_comm a' a] at h6
    rw [dist_comm q v] at h5
    rw [q1] at h2 h5
    simp only [← hαd, ← hβd] at h2 h5 h6
    have h8 := mul_le_mul_of_nonneg_left h6 hτ0.le
    have e1 : τ * β = c * (σ * α) := by rw [hτ, hσ]; ring
    have e2 : (τ * β) ^ 2 = c ^ 2 * (σ * α) ^ 2 := by rw [e1]; ring
    have e3 : (τ * β) ^ 2 = c * (σ * α) * (τ * β) := by rw [sq, ← e1]
    have h7 : (σ * τ) * (α ^ 2 + β ^ 2 - dist a a' ^ 2) ≤ (σ * τ) * (2 * c * (α * β)) := by
      nlinarith
    linarith [le_of_mul_le_mul_left h7 (by positivity)]
  refine angle_num (α := α) (β := β) (A := dist z v ^ 2) hr hr' hα hβ (by linarith) (by linarith) hQ ?_
  -- Lemma lem:toolkit (a) twice, for the points at η on [a,a′] and at t on [z,v]
  intro η t hη0 hη1 ht0 ht1
  obtain ⟨m, -, -, hm⟩ := (lem_toolkit (Y := Z)).1 a a' η hη0 hη1
  obtain ⟨g, -, -, hg⟩ := (lem_toolkit (Y := Z)).1 z v t ht0 ht1
  have h1 := mul_le_mul_of_nonneg_left (hm z) (show 0 ≤ 1 - t by linarith)
  have h2 := mul_le_mul_of_nonneg_left (hm v) ht0
  have h3 := hg m
  rw [dist_comm m z, dist_comm m v] at h3
  simp only [← hαd, ← hβd] at h2 ⊢
  linarith [sq_nonneg (dist m g)]

/-- **Paper: Lemma lem:angle.** "Let u, p, ζ be as in Lemma lem:tele, 0 ≤ ζ ≤ 1, and 1−c² ≤ (1−ζ)², c > 0. If a, a′
are the projections of z for [p,p+2u) and [p+u,p+3u), then |aa′|² ≤ |za|² + |za′|² + 2c|za||za′|." -/
theorem lem_angle {μ : ℕ} {s : ℝ} {h : ℕ} {Z : Type} [MetricSpace Z] [Cat.CN Z] (A : IsoAct (U h) Z)
    (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) (hA : ∀ z, Contr (A.len z) μ s) {u p : ℕ} {ζ c : ℝ}
    (hu : 2 ≤ u) (hp : p + 3 * u ≤ h) (hζ : 0 ≤ ζ)
    (hC : 4 * windowConst μ s (3 * u) ≤ ζ ^ 2 * ((u : ℝ) - 1) ^ 2) (hζ1 : ζ ≤ 1)
    (hcζ : 1 - c ^ 2 ≤ (1 - ζ) ^ 2) (hc : 0 < c) (z : Z) :
    dist ((A.W p (2 * u)).P z) ((A.W (p + u) (2 * u)).P z) ^ 2 ≤
      dist z ((A.W p (2 * u)).P z) ^ 2 + dist z ((A.W (p + u) (2 * u)).P z) ^ 2 +
        2 * c * (dist z ((A.W p (2 * u)).P z) * dist z ((A.W (p + u) (2 * u)).P z)) := by
  set a := (A.W p (2 * u)).P z with ha
  set v := (A.W p (3 * u)).P a with hv
  have hvf : (A.W p (3 * u)).Fix v := IsoAct.P_fix _ a
  have hv1 : (A.W p (2 * u)).Fix v := hvf.sub A le_rfl (by omega) hp
  refine lem_angle_projections _ _ hc z v hv1 (hvf.sub A (by omega) (by omega) hp) fun q σ hσ0 hσ1 q1 q2 => ?_
  have hqf : (A.W p (2 * u)).Fix q := segment_fixed _ hσ0.le hσ1 hv1 (IsoAct.P_fix _ z) q1 q2
  have hqv : (A.W p (3 * u)).P q = v := projection_segment _ q1 q2
  have h1 := lem_tele A hμ hs hsm hA hu hp hζ hC hqf
  rw [hqv] at h1
  rw [dist_comm v q]
  calc (1 - c ^ 2) * dist q v ^ 2 ≤ ((1 - ζ) * dist q v) ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right hcζ (sq_nonneg _)
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (by linarith) dist_nonneg) h1 2

/-- The proof of Theorem thm:poincare: "If the windows of i, i′ do not meet and y is fixed by that of i, then the
point nearest to y among those fixed by that of i′ is fixed by both. So this point can serve as v in the proof of Lemma
lem:angle, with ζ = 0 and any c > 0, and gives |Q_iz Q_{i′}z|² ≤ r_i² + r_{i′}²." -/
theorem thm_poincare_far {h : ℕ} {Z : Type} [MetricSpace Z] [Cat.CN Z] (A : IsoAct (U h) Z) {p n p' n' : ℕ}
    (hd : p + n ≤ p') (hp' : p' + n' ≤ h) (z : Z) :
    dist ((A.W p n).P z) ((A.W p' n').P z) ^ 2 ≤
      dist z ((A.W p n).P z) ^ 2 + dist z ((A.W p' n').P z) ^ 2 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set r := dist z ((A.W p n).P z) * dist z ((A.W p' n').P z) with hr
  have hr0 : 0 ≤ r := mul_nonneg dist_nonneg dist_nonneg
  have hc : 0 < ε / (2 * r + 1) := by positivity
  set v := (A.W p' n').P ((A.W p n).P z) with hv
  have hv1 : (A.W p n).Fix v := (windows_commute A hd hp').1 _ (IsoAct.P_fix _ z)
  refine (lem_angle_projections _ _ hc z v hv1 (IsoAct.P_fix _ _) fun q σ hσ0 hσ1 q1 q2 => ?_).trans ?_
  · rw [projection_segment _ q1 q2, ← hv, dist_comm q v]
    exact mul_le_of_le_one_left (sq_nonneg _) (by linarith [sq_nonneg (ε / (2 * r + 1))])
  · rw [← hr]
    have : 2 * (ε / (2 * r + 1)) * r ≤ ε := by
      rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith

section Poincare

variable {μ : ℕ} {s : ℝ} {h : ℕ} {Z : Type} [MetricSpace Z] [Cat.CN Z] (A : IsoAct (U h) Z)

/-- F(z) = ∑_i r_i², r_i = |z Q_iz|, Q_i the projection for the window [iu, iu+2u), i < L. -/
noncomputable def windowSum (u L : ℕ) (z : Z) : ℝ := ∑ i : Fin L, dist z ((A.W (i.1 * u) (2 * u)).P z) ^ 2

theorem windowSum_nonneg (u L : ℕ) (z : Z) : 0 ≤ windowSum A u L z := sum_nonneg fun _ _ => sq_nonneg _

theorem window_le {u L : ℕ} (hh : (L + 1) * u = h) (a : Fin L) : a.1 * u + 2 * u ≤ h := by
  rw [← hh]
  calc a.1 * u + 2 * u = (a.1 + 2) * u := by ring
    _ ≤ (L + 1) * u := Nat.mul_le_mul_right u (by omega)

/-- The proof of Theorem thm:poincare: "For neighbours Lemma lem:angle allows c(r_i²+r_{i′}²) more", so
∑_{i,i′} |Q_iz Q_{i′}z|² ≤ 2(L−1+2c)F(z). -/
theorem thm_poincare_pairs (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) (hA : ∀ z, Contr (A.len z) μ s) {u L : ℕ}
    {ζ c : ℝ} (hu : 2 ≤ u) (hh : (L + 1) * u = h) (hζ : 0 ≤ ζ)
    (hC : 4 * windowConst μ s (3 * u) ≤ ζ ^ 2 * ((u : ℝ) - 1) ^ 2) (hζ1 : ζ ≤ 1)
    (hcζ : 1 - c ^ 2 ≤ (1 - ζ) ^ 2) (hc0 : 0 < c) (z : Z) :
    ∑ a : Fin L, ∑ b : Fin L, dist ((A.W (a.1 * u) (2 * u)).P z) ((A.W (b.1 * u) (2 * u)).P z) ^ 2 ≤
      2 * ((L : ℝ) - (1 - 2 * c)) * windowSum A u L z := by
  set Q : Fin L → Z → Z := fun a z => (A.W (a.1 * u) (2 * u)).P z with hQ
  show ∑ a, ∑ b, dist (Q a z) (Q b z) ^ 2 ≤ _
  have hwin := window_le hh (L := L)
  have hpair : ∀ (z : Z) (a b : Fin L), a.1 < b.1 → dist (Q a z) (Q b z) ^ 2 ≤
      dist z (Q a z) ^ 2 + dist z (Q b z) ^ 2 +
        if b.1 = a.1 + 1 then c * (dist z (Q a z) ^ 2 + dist z (Q b z) ^ 2) else 0 := by
    intro z a b hab
    split_ifs with hb
    · have h3 : a.1 * u + 3 * u ≤ h := by
        have := hwin b
        rw [hb] at this
        nlinarith
      have h1 := lem_angle A hμ hs hsm hA hu h3 hζ hC hζ1 hcζ hc0 z
      rw [show a.1 * u + u = b.1 * u by rw [hb]; ring] at h1
      have h2 : 2 * c * (dist z (Q a z) * dist z (Q b z)) ≤
          c * (dist z (Q a z) ^ 2 + dist z (Q b z) ^ 2) := by
        nlinarith [sq_nonneg (dist z (Q a z) - dist z (Q b z))]
      exact h1.trans (by linarith)
    · have h3 : a.1 * u + 2 * u ≤ b.1 * u := by
        calc a.1 * u + 2 * u = (a.1 + 2) * u := by ring
          _ ≤ b.1 * u := Nat.mul_le_mul_right u (by omega)
      rw [add_zero]
      exact thm_poincare_far A h3 (hwin b) z
  have hpair2 : ∀ (z : Z) (a b : Fin L), dist (Q a z) (Q b z) ^ 2 ≤
      (if a = b then 0 else dist z (Q a z) ^ 2 + dist z (Q b z) ^ 2) +
        ((if b.1 = a.1 + 1 then c * (dist z (Q a z) ^ 2 + dist z (Q b z) ^ 2) else 0) +
          if a.1 = b.1 + 1 then c * (dist z (Q a z) ^ 2 + dist z (Q b z) ^ 2) else 0) := by
    intro z a b
    rcases lt_trichotomy a.1 b.1 with hab | hab | hab
    · rw [if_neg (fun h => by rw [h] at hab; exact lt_irrefl _ hab),
        if_neg (show ¬ a.1 = b.1 + 1 by omega), add_zero]
      exact hpair z a b hab
    · have : a = b := Fin.ext hab
      subst this
      simp
    · rw [if_neg (fun h => by rw [h] at hab; exact lt_irrefl _ hab),
        if_neg (show ¬ b.1 = a.1 + 1 by omega), zero_add, dist_comm]
      have := hpair z b a hab
      rw [add_comm (dist z (Q b z) ^ 2)] at this
      exact this
  have hnb : ∀ (r : Fin L → ℝ) (_ : ∀ a, 0 ≤ r a), ∑ a : Fin L, ∑ b : Fin L,
      (if b.1 = a.1 + 1 then c * (r a + r b) else 0) ≤ 2 * c * ∑ a, r a := by
    intro r hr
    have e1 : ∀ a : Fin L, ∑ b : Fin L, (if b.1 = a.1 + 1 then c * r a else 0) ≤ c * r a := by
      intro a
      by_cases ha : a.1 + 1 < L
      · rw [sum_eq_single (⟨a.1 + 1, ha⟩ : Fin L)]
        · simp
        · intro b _ hb
          rw [if_neg]
          intro h1
          exact hb (Fin.ext h1)
        · simp
      · rw [sum_eq_zero]
        · exact mul_nonneg hc0.le (hr a)
        · intro b _
          rw [if_neg]
          have := b.2
          omega
    have e2 : ∀ b : Fin L, ∑ a : Fin L, (if b.1 = a.1 + 1 then c * r b else 0) ≤ c * r b := by
      intro b
      by_cases hb : 1 ≤ b.1
      · rw [sum_eq_single (⟨b.1 - 1, by omega⟩ : Fin L)]
        · rw [if_pos (by simp only; omega)]
        · intro a _ ha
          rw [if_neg]
          intro h1
          apply ha
          apply Fin.ext
          simp only
          omega
        · simp
      · rw [sum_eq_zero]
        · exact mul_nonneg hc0.le (hr b)
        · intro a _
          rw [if_neg]
          omega
    have e3 : ∀ a b : Fin L, (if b.1 = a.1 + 1 then c * (r a + r b) else 0) =
        (if b.1 = a.1 + 1 then c * r a else 0) + if b.1 = a.1 + 1 then c * r b else 0 := by
      intro a b
      split_ifs
      · ring
      · simp
    simp only [e3, sum_add_distrib]
    rw [sum_comm (f := fun a b : Fin L => if b.1 = a.1 + 1 then c * r b else 0)]
    have e4 := sum_le_sum fun a (_ : a ∈ univ) => e1 a
    have e5 := sum_le_sum fun b (_ : b ∈ univ) => e2 b
    rw [← mul_sum] at e4 e5
    linarith
  set r : Fin L → ℝ := fun a => dist z (Q a z) ^ 2 with hr
  have hr0 : ∀ a, 0 ≤ r a := fun a => sq_nonneg _
  have h1 : ∑ a : Fin L, ∑ b : Fin L, (if a = b then (0 : ℝ) else r a + r b) =
      2 * ((L : ℝ) - 1) * ∑ a, r a := by
    have e1 : ∀ a b : Fin L, (if a = b then (0 : ℝ) else r a + r b) =
        (r a + r b) - if a = b then 2 * r a else 0 := by
      intro a b
      split_ifs with hab
      · rw [hab]; ring
      · ring
    simp only [e1, sum_sub_distrib, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, sum_ite_eq, mem_univ, if_true, ← mul_sum]
    ring
  have h2 := hnb r hr0
  have h3 : ∑ a : Fin L, ∑ b : Fin L, (if a.1 = b.1 + 1 then c * (r a + r b) else 0) ≤
      2 * c * ∑ a, r a := by
    rw [sum_comm]
    refine le_trans (le_of_eq ?_) h2
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [add_comm (r b)]
  calc ∑ a, ∑ b, dist (Q a z) (Q b z) ^ 2 ≤ _ :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => hpair2 z a b
    _ = ∑ a : Fin L, ∑ b : Fin L, (if a = b then (0 : ℝ) else r a + r b) +
        (∑ a : Fin L, ∑ b : Fin L, (if b.1 = a.1 + 1 then c * (r a + r b) else 0) +
          ∑ a : Fin L, ∑ b : Fin L, (if a.1 = b.1 + 1 then c * (r a + r b) else 0)) := by
        simp only [sum_add_distrib]
        rfl
    _ ≤ _ := by
        rw [h1]
        show _ ≤ 2 * ((L : ℝ) - (1 - 2 * c)) * ∑ a, r a
        linarith

/-- The proof of Theorem thm:poincare: for the barycenter b of the points Q_iz, "F(b) ≤ ∑_i|b Q_iz|² ≤ (1 − (1−2c)/L)F(z)
and L|zb|² ≤ F(z) − F(b)", by Lemma lem:toolkit(c). -/
theorem thm_poincare_step (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) (hA : ∀ z, Contr (A.len z) μ s) {u L : ℕ}
    {ζ c : ℝ} (hu : 2 ≤ u) (hL : 1 ≤ L) (hh : (L + 1) * u = h) (hζ : 0 ≤ ζ)
    (hC : 4 * windowConst μ s (3 * u) ≤ ζ ^ 2 * ((u : ℝ) - 1) ^ 2) (hζ1 : ζ ≤ 1)
    (hcζ : 1 - c ^ 2 ≤ (1 - ζ) ^ 2) (hc0 : 0 < c) (z : Z) :
    ∃ b, windowSum A u L b ≤ (1 - (1 - 2 * c) / L) * windowSum A u L z ∧
      (L : ℝ) * dist z b ^ 2 ≤ windowSum A u L z - windowSum A u L b := by
  set Q : Fin L → Z := fun a => (A.W (a.1 * u) (2 * u)).P z with hQ
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  obtain ⟨b, hb⟩ := (lem_toolkit (Y := Z)).2.2.1.1 L Q hL
  have h1 : 2 * ((L : ℝ) * ∑ i, dist b (Q i) ^ 2) ≤ ∑ i, ∑ j, dist (Q i) (Q j) ^ 2 := by
    refine le_trans (le_of_eq ?_) (sum_le_sum fun i _ => hb (Q i))
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum,
      sum_congr rfl fun i _ => congrArg (· ^ 2) (dist_comm (Q i) b)]
    ring
  have h2 := h1.trans (thm_poincare_pairs A hμ hs hsm hA hu hh hζ hC hζ1 hcζ hc0 z)
  have h3 : ∑ i, dist b (Q i) ^ 2 ≤ (1 - (1 - 2 * c) / L) * windowSum A u L z := by
    refine le_of_mul_le_mul_left ?_ hLr
    have e : (L : ℝ) * ((1 - (1 - 2 * c) / L) * windowSum A u L z) = (L - (1 - 2 * c)) * windowSum A u L z := by
      field_simp
    rw [e]
    linarith
  have h4 : windowSum A u L b ≤ ∑ i, dist b (Q i) ^ 2 :=
    sum_le_sum fun a _ => pow_le_pow_left₀ dist_nonneg
      ((projection_nearest _ b).2.1 _ (IsoAct.P_fix _ z)) 2
  refine ⟨b, h4.trans h3, ?_⟩
  have h5 := hb z
  have e : windowSum A u L z = ∑ i, dist z (Q i) ^ 2 := rfl
  linarith

/-- The proof of Theorem thm:poincare: "Iterate: F decreases geometrically and the steps add up to at most
2√(F(z)/(1−2c)), so the points converge to one fixed by every window, hence by U_h. So |z P_{[0,h)}z|² ≤ 4F(z)/(1−2c)." -/
theorem thm_poincare_limit (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) (hA : ∀ z, Contr (A.len z) μ s) {u L : ℕ}
    {ζ c : ℝ} (hu : 2 ≤ u) (hL : 1 ≤ L) (hh : (L + 1) * u = h) (hζ : 0 ≤ ζ)
    (hC : 4 * windowConst μ s (3 * u) ≤ ζ ^ 2 * ((u : ℝ) - 1) ^ 2) (hζ1 : ζ ≤ 1)
    (hcζ : 1 - c ^ 2 ≤ (1 - ζ) ^ 2) (hc0 : 0 < c) (hc : c < 1 / 2) (z : Z) :
    ∃ y, A.Fix y ∧ dist z y ^ 2 ≤ 4 / (1 - 2 * c) * windowSum A u L z := by
  choose b hb1 hb2 using thm_poincare_step A hμ hs hsm hA hu hL hh hζ hC hζ1 hcζ hc0
  set F := windowSum A u L with hF
  have hF0 : ∀ z, 0 ≤ F z := windowSum_nonneg A u L
  set δ := 1 - 2 * c with hδ
  have hδ0 : 0 < δ := by linarith
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hq0 : 0 ≤ 1 - δ / L := by
    have : δ / L ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    linarith
  have hq1 : 1 - δ / L < 1 := by
    have : 0 < δ / L := by positivity
    linarith
  set y : ℕ → Z := fun n => b^[n] z with hy
  have hys : ∀ n, y (n + 1) = b (y n) := fun n => Function.iterate_succ_apply' b n z
  set X : ℕ → ℝ := fun n => 2 / √δ * √(F (y n)) with hX
  have hstep : ∀ n, dist (y n) (y (n + 1)) ≤ X n - X (n + 1) := by
    intro n
    rw [hys, hX]
    simp only [hys, ← mul_sub]
    exact step_num (L := (L : ℝ)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hLr hδ0
      (by rw [Real.sq_sqrt (hF0 _), Real.sq_sqrt (hF0 _)]; exact hb1 _)
      (by rw [Real.sq_sqrt (hF0 _), Real.sq_sqrt (hF0 _)]; exact hb2 _)
  have htot : ∀ n m, n ≤ m → dist (y n) (y m) ≤ X n - X m := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m _ ih =>
      have := dist_triangle (y n) (y m) (y (m + 1))
      linarith [hstep m]
  have hX0 : ∀ n, 0 ≤ X n := fun n => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hgeo : ∀ n, F (y n) ≤ (1 - δ / L) ^ n * F z := by
    intro n
    induction n with
    | zero => simp [hy]
    | succ n ih =>
      rw [hys, pow_succ']
      refine (hb1 _).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ih hq0
  have hF0lim : Tendsto (fun n => F (y n)) atTop (nhds 0) := by
    refine squeeze_zero (fun n => hF0 _) hgeo ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (F z)
  have hX0lim : Tendsto X atTop (nhds 0) := by
    simpa using (hF0lim.sqrt).const_mul (2 / √δ)
  have hcauchy : CauchySeq y :=
    cauchySeq_of_le_tendsto_0' X (fun n m hnm => (htot n m hnm).trans (by linarith [hX0 m])) hX0lim
  obtain ⟨y₀, hy₀⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨y₀, ?_, ?_⟩
  · -- F is continuous, so the limit is fixed by every window
    have hcont : Continuous F := by
      rw [hF]
      unfold windowSum
      refine continuous_finsetSum _ fun a _ => Continuous.pow ?_ 2
      refine (LipschitzWith.of_le_add fun x w => ?_).continuous
      have h1 := (projection_nearest (A.W (a.1 * u) (2 * u)) x).2.1 _ (IsoAct.P_fix _ w)
      have h2 := dist_triangle x w ((A.W (a.1 * u) (2 * u)).P w)
      linarith
    have hlim : F y₀ = 0 := tendsto_nhds_unique ((hcont.tendsto y₀).comp hy₀) hF0lim
    have hfix : ∀ a : Fin L, (A.W (a.1 * u) (2 * u)).Fix y₀ := fun a => by
      have h1 : dist y₀ ((A.W (a.1 * u) (2 * u)).P y₀) ^ 2 = 0 :=
        (sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 hlim a (mem_univ a)
      rw [dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)]
      exact IsoAct.P_fix _ _
    let H : Subgroup (U h) :=
      { carrier := {g | A.act g y₀ = y₀}
        one_mem' := A.one' y₀
        mul_mem' := fun {g g'} hg hg' => by
          show A.act (g * g') y₀ = y₀
          rw [A.mul', show A.act g' y₀ = y₀ from hg', show A.act g y₀ = y₀ from hg]
        inv_mem' := fun {g} hg => by
          show A.act g⁻¹ y₀ = y₀
          conv_lhs => rw [← show A.act g y₀ = y₀ from hg]
          rw [← A.mul', inv_mul_cancel, A.one'] }
    refine fun g => mem_of_x H (fun j => ?_) g
    show A.act (x h j) y₀ = y₀
    have hjlt := j.2
    obtain ⟨j, hj⟩ := j
    simp only at hjlt ⊢
    have h3 : ∃ a : Fin L, a.1 * u ≤ j ∧ j + 2 ≤ a.1 * u + 2 * u := by
      by_cases hj2 : j < u
      · refine ⟨⟨0, by omega⟩, by simp, ?_⟩
        simp only [zero_mul, zero_add]
        omega
      · have hdiv := Nat.div_add_mod (j - (u - 1)) u
        have hmod := Nat.mod_lt (j - (u - 1)) (show 0 < u by omega)
        refine ⟨⟨(j - (u - 1)) / u, ?_⟩, ?_, ?_⟩
        · rw [Nat.div_lt_iff_lt_mul (by omega)]
          have : (L + 1) * u = L * u + u := by ring
          omega
        · simp only
          rw [mul_comm]
          omega
        · simp only
          rw [mul_comm]
          omega
    obtain ⟨a, ha1, ha2⟩ := h3
    have he := A.e_zero (hfix a) ha1 ha2 (window_le hh a)
    unfold IsoAct.e at he
    rw [dif_pos hj] at he
    exact (dist_eq_zero.1 he).symm
  · have h1 : dist z y₀ ≤ X 0 := le_of_tendsto' ((tendsto_const_nhds (x := z)).dist hy₀) fun n => by
      have := htot 0 n (Nat.zero_le n)
      simp only [hy, Function.iterate_zero, id_eq] at this
      linarith [hX0 n]
    calc dist z y₀ ^ 2 ≤ X 0 ^ 2 := pow_le_pow_left₀ dist_nonneg h1 2
      _ = 4 / δ * F z := by
        simp only [hX, hy, Function.iterate_zero, id_eq]
        rw [mul_pow, div_pow, Real.sq_sqrt hδ0.le, Real.sq_sqrt (hF0 z)]
        norm_num

/-- The proof of Theorem thm:poincare: "(eq:window) for n = 2u, each generator lying in at most two windows, bounds
F(z) by 2C(2u) ∑_j e_j(z)²." -/
theorem thm_poincare_windows (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) (hA : ∀ z, Contr (A.len z) μ s) {u L : ℕ}
    (hu : 2 ≤ u) (hh : (L + 1) * u = h) (z : Z) :
    windowSum A u L z ≤ 2 * windowConst μ s (2 * u) * ∑ j ∈ range (h - 1), A.e j z ^ 2 := by
  set Q : Fin L → Z → Z := fun a z => (A.W (a.1 * u) (2 * u)).P z with hQ
  set F : Z → ℝ := windowSum A u L with hF
  set C₂ := windowConst μ s (2 * u) with hC₂d
  have hwin := window_le hh (L := L)
  have h1 : ∀ a : Fin L, dist z (Q a z) ^ 2 ≤ C₂ * ∑ j ∈ range (h - 1),
      if a.1 * u ≤ j ∧ j + 1 < a.1 * u + 2 * u then A.e j z ^ 2 else 0 := by
    intro a
    refine (eq_window A hμ hs hsm hA (hwin a) z).trans (le_of_eq ?_)
    rw [← sum_filter]
    congr 1
    refine sum_congr ?_ fun _ _ => rfl
    have := hwin a
    ext j
    simp only [mem_Ico, mem_filter, mem_range]
    omega
  have h2 : F z ≤ C₂ * ∑ j ∈ range (h - 1), ∑ a : Fin L,
      if a.1 * u ≤ j ∧ j + 1 < a.1 * u + 2 * u then A.e j z ^ 2 else 0 := by
    rw [sum_comm, mul_sum]
    exact sum_le_sum fun a _ => h1 a
  refine h2.trans ?_
  rw [mul_comm 2 C₂, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (windowConst_nonneg μ s _)
  rw [mul_sum]
  refine sum_le_sum fun j _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have h3 : (univ.filter fun a : Fin L => a.1 * u ≤ j ∧ j + 1 < a.1 * u + 2 * u).card ≤ 2 := by
    have hsub : (univ.filter fun a : Fin L => a.1 * u ≤ j ∧ j + 1 < a.1 * u + 2 * u).image
        (fun a => a.1) ⊆ {j / u - 1, j / u} := by
      intro k hk
      simp only [mem_image, mem_filter, mem_univ, true_and] at hk
      obtain ⟨a, ⟨ha1, ha2⟩, rfl⟩ := hk
      have h4 : a.1 ≤ j / u := (Nat.le_div_iff_mul_le (by omega)).2 ha1
      have h5 : j / u < a.1 + 2 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc j < a.1 * u + 2 * u := by omega
          _ = (a.1 + 2) * u := by ring
      simp only [mem_insert, mem_singleton]
      omega
    calc _ = ((univ.filter fun a : Fin L => a.1 * u ≤ j ∧ j + 1 < a.1 * u + 2 * u).image
        (fun a => a.1)).card := (card_image_of_injective _ Fin.val_injective).symm
      _ ≤ ({j / u - 1, j / u} : Finset ℕ).card := card_le_card hsub
      _ ≤ 2 := card_le_two
  exact_mod_cast h3

/-- The Poincaré bound for every isometric action of U_h, h = lu, on a CAT(0) space with contracting lengths, from the
proof of Theorem thm:poincare, with ζ = 1/32 and c = 1/4: "|z,gz| ≤ 2|z P_{[0,h)}z|", so E_g|z,gz|² ≤ 32C(2u)/(1−2c) ∑_j e_j(z)². -/
theorem thm_poincare_action (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) (hA : ∀ z, Contr (A.len z) μ s) {u l : ℕ}
    (hu : 2 ≤ u) (hl : 2 ≤ l) (hh : l * u = h)
    (hC : 4 * windowConst μ s (3 * u) ≤ (1 / 32) ^ 2 * ((u : ℝ) - 1) ^ 2) (z : Z) :
    (∑ g, dist z (A.act g z) ^ 2) / Fintype.card (U h) ≤
      32 * windowConst μ s (2 * u) / (1 - 2 * (1 / 4)) * ∑ j, dist z (A.act (x h j) z) ^ 2 := by
  obtain ⟨L, rfl⟩ : ∃ L, l = L + 1 := ⟨l - 1, by omega⟩
  obtain ⟨y, hy, hy2⟩ := thm_poincare_limit A hμ hs hsm hA hu (by omega) hh (by norm_num) hC (by norm_num)
    (c := 1 / 4) (by norm_num) (by norm_num) (by norm_num) z
  have hw := thm_poincare_windows A hμ hs hsm hA hu hh z
  have hd : ∀ g, dist z (A.act g z) ^ 2 ≤ 4 * dist z y ^ 2 := fun g => by
    have h1 := dist_triangle z y (A.act g z)
    have h2 : dist y (A.act g z) = dist z y := by
      conv_lhs => rw [← hy g]
      rw [A.iso', dist_comm]
    rw [h2] at h1
    calc dist z (A.act g z) ^ 2 ≤ (2 * dist z y) ^ 2 := pow_le_pow_left₀ dist_nonneg (by linarith) 2
      _ = _ := by ring
  have hsum : ∑ j ∈ range (h - 1), A.e j z ^ 2 = ∑ j, dist z (A.act (x h j) z) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => A.e j z ^ 2)]
    refine sum_congr rfl fun j _ => ?_
    unfold IsoAct.e
    rw [dif_pos j.2]
  rw [hsum] at hw
  rw [div_le_iff₀ (by exact_mod_cast Fintype.card_pos)]
  refine (sum_le_card_nsmul univ _ _ fun g _ => hd g).trans ?_
  rw [card_univ, nsmul_eq_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  norm_num at hy2 ⊢
  linarith

end Poincare

/-- The proof of Theorem thm:poincare: "Since C(n) = o(n²), some u has 4C(3u) ≤ (u−1)²/32²; fix it." -/
theorem thm_poincare_size {μ : ℕ} {s : ℝ} (hμ : 2 ≤ μ) (hs : 1 ≤ s) (hsm : s ^ 2 < μ) :
    ∃ u : ℕ, 2 ≤ u ∧ 4 * windowConst μ s (3 * u) ≤ (1 / 32) ^ 2 * ((u : ℝ) - 1) ^ 2 := by
  obtain ⟨n₀, hn⟩ := eventually_atTop.1
    ((lem_first hμ hs hsm).1.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (36 * 4096) by norm_num)))
  refine ⟨n₀ + 2, by omega, ?_⟩
  have h1 := hn (3 * (n₀ + 2)) (by omega)
  have hpos : (0 : ℝ) < ((3 * (n₀ + 2) : ℕ) : ℝ) ^ 2 := by positivity
  rw [div_lt_iff₀ hpos] at h1
  rw [windowConst]
  push_cast at h1 ⊢
  nlinarith [show (0 : ℝ) ≤ n₀ from Nat.cast_nonneg _]

/-- **Paper: Theorem thm:poincare.** "There are u ≥ 2 and C₀ such that for every l ≥ 2, h = lu, and every price on U_h,
E_{g,k}|k,gk|² ≤ C₀ ∑_{j<h−1} E_k|k,x_jk|²." In the proof Z = L²(U_h,Y) has the sum for the mean; this scales all
distances by one factor. C₀ = 32C(2u)/(1−2c). -/
theorem thm_poincare {K : Type} [Field K] (hK : Contracting K) :
    ∃ u : ℕ, 2 ≤ u ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ l : ℕ, 2 ≤ l → ∀ w : U (l * u) → U (l * u) → ℝ, Nc.Price.IsPrice K w →
      (∑ g, ∑ k, w k (g * k) ^ 2) / (Fintype.card (U (l * u)) : ℝ) ^ 2 ≤
        C₀ * ∑ j, (∑ k, w k (x (l * u) j * k) ^ 2) / (Fintype.card (U (l * u)) : ℝ) := by
  obtain ⟨μ, s, hμ, hs, hsm, hcase⟩ := hK
  obtain ⟨u, hu, hC⟩ := thm_poincare_size hμ hs hsm
  refine ⟨u, hu, 32 * windowConst μ s (2 * u) / (1 - 2 * (1 / 4)),
    div_nonneg (by have := windowConst_nonneg μ s (2 * u); linarith) (by norm_num), fun l hl w hw => ?_⟩
  have hb : (0 : ℝ) < Fintype.card (U (l * u)) := by exact_mod_cast Fintype.card_pos
  obtain ⟨Y, hYm, hYc, f, hY, hf⟩ := prop_space hw
  have hCN : Cat.CN (PiLp 2 fun _ : U (l * u) => Y) := (lem_toolkit (Y := Y)).2.2.2.2.1 _
  have hA : ∀ z : PiLp 2 fun _ : U (l * u) => Y, Contr ((transAct (U (l * u)) Y).len z) μ s := by
    intro z
    obtain ⟨len, hlen, hcon⟩ := lengths_of_maps (by omega) (by linarith) hcase hY (fun k => z k)
    refine contracts_smul len _ (by omega) (c := √(Fintype.card (U (l * u)) : ℝ)) (fun g => ?_) hcon
    rw [hlen, Real.sqrt_div' _ hb.le, mul_div_cancel₀ _ (Real.sqrt_pos.2 hb).ne', IsoAct.len_val,
      ← Real.sqrt_sq (dist_nonneg (x := z) (y := (transAct (U (l * u)) Y).act g z)), transAct_dist]
    exact congrArg _ (sum_congr rfl fun k _ => by rw [dist_comm])
  have h1 := thm_poincare_action (transAct (U (l * u)) Y) hμ hs hsm hA hu hl rfl hC (WithLp.toLp 2 f)
  have h2 : ∀ g : U (l * u), dist (WithLp.toLp 2 f : PiLp 2 fun _ : U (l * u) => Y)
      ((transAct (U (l * u)) Y).act g (WithLp.toLp 2 f)) ^ 2 = ∑ k, w k (g * k) ^ 2 := by
    intro g
    rw [transAct_dist]
    refine sum_congr rfl fun k _ => ?_
    show dist (f (g * k)) (f k) ^ 2 = _
    rw [dist_comm, hf]
  simp only [h2] at h1
  rw [pow_two, ← div_div, ← Finset.sum_div, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right h1 hb.le

/-- The inequality of Theorem thm:poincare for the numbers u and C₀: for every l ≥ 2, h = lu, and every price on U_h,
E_{g,k}|k,gk|² ≤ C₀ ∑_j E_k|k,x_jk|². -/
def PoincareBound (K : Type) [Field K] (u : ℕ) (C₀ : ℝ) : Prop :=
  ∀ l : ℕ, 2 ≤ l → ∀ w : U (l * u) → U (l * u) → ℝ, Nc.Price.IsPrice K w →
    (∑ g, ∑ k, w k (g * k) ^ 2) / (Fintype.card (U (l * u)) : ℝ) ^ 2 ≤
      C₀ * ∑ j, (∑ k, w k (x (l * u) j * k) ^ 2) / (Fintype.card (U (l * u)) : ℝ)

end Paper

end

theorem solution {K : Type} [Field K] (hK : Paper.Contracting K) :
    ∃ u : ℕ, 2 ≤ u ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ l : ℕ, 2 ≤ l → ∀ w : U (l * u) → U (l * u) → ℝ, Nc.Price.IsPrice K w →
      (∑ g, ∑ k, w k (g * k) ^ 2) / (Fintype.card (U (l * u)) : ℝ) ^ 2 ≤
        C₀ * ∑ j, (∑ k, w k (x (l * u) j * k) ^ 2) / (Fintype.card (U (l * u)) : ℝ) := Paper.thm_poincare hK
