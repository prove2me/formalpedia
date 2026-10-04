-- Prove2me | solution 2 for VanderbeiLP.Simplex.lex_pivot_increases_perturbed_objective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T22:31:42.116696+00:00
-- url     : https://prove2.me/submissions/1a470e71-e5bb-4f5c-97b2-a74e05d6f1fa

import Mathlib
import Definitions.Def_VanderbeiLP_Simplex_PivotRules

set_option autoImplicit false

namespace VanderbeiLP.Simplex.LexObj4697

open VanderbeiLP.Simplex

variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}

/-- coordinates of `v` in the basis of `D`, extended by zero. -/
noncomputable def coordF (D : Dictionary A) (v : Fin m → ℝ) (i : Fin (n + m)) : ℝ :=
  if h : i ∈ D.B then D.colBasis.repr v ⟨i, h⟩ else 0

lemma coordF_not_mem (D : Dictionary A) (v : Fin m → ℝ) {i : Fin (n + m)} (h : i ∉ D.B) :
    coordF D v i = 0 := by
  simp [coordF, h]

lemma sum_coordF (D : Dictionary A) (v : Fin m → ℝ) :
    ∑ j, coordF D v j • augCol A j = v := by
  have h1 : ∑ j, coordF D v j • augCol A j = ∑ j ∈ D.B, coordF D v j • augCol A j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    simp [coordF_not_mem D v hj]
  rw [h1, ← Finset.sum_coe_sort]
  conv_rhs => rw [← D.colBasis.sum_repr v]
  apply Finset.sum_congr rfl
  intro j _
  have hc : (D.colBasis : D.B → Fin m → ℝ) j = augCol A (j : Fin (n + m)) := by
    unfold Dictionary.colBasis
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  rw [hc]
  simp [coordF, j.2]

lemma eq_zero_of_supp (D : Dictionary A) (f : Fin (n + m) → ℝ)
    (hsupp : ∀ j, j ∉ D.B → f j = 0) (hsum : ∑ j, f j • augCol A j = 0) :
    ∀ j, f j = 0 := by
  have h1 : ∑ j, f j • augCol A j = ∑ j ∈ D.B, f j • augCol A j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    simp [hsupp j hj]
  rw [h1, ← Finset.sum_coe_sort] at hsum
  have hli := D.linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  have := hli (fun j : D.B => f j) hsum
  intro j
  by_cases hj : j ∈ D.B
  · exact this ⟨j, hj⟩
  · exact hsupp j hj

lemma exchange (D D' : Dictionary A) (c : Fin n → ℝ) (k l : Fin (n + m))
    (hk : k ∉ D.B) (hl : l ∈ D.B) (hlk : D.abar l k ≠ 0)
    (hB : D'.B = insert k (D.B.erase l)) (v : Fin m → ℝ) :
    ∑ i ∈ D'.B, extCost c i * coordF D' v i =
      ∑ i ∈ D.B, extCost c i * coordF D v i +
        (D.cbar c k / D.abar l k) * coordF D v l := by
  set x := coordF D v with hx
  set x' := coordF D' v with hx'
  set w : Fin (n + m) → ℝ := fun j => (if j = k then 1 else 0) - coordF D (augCol A k) j with hw
  set t := x' k - x k with ht
  have habar : ∀ i, D.abar i k = coordF D (augCol A k) i := fun i => rfl
  have hz := eq_zero_of_supp D (fun j => (x' j - x j) - t * w j) ?_ ?_
  rotate_left
  · intro j hj
    by_cases hjk : j = k
    · subst hjk
      simp [hw, ht, coordF_not_mem D _ hj]
    · have hj' : j ∉ D'.B := by
        rw [hB]; intro h
        rcases Finset.mem_insert.1 h with h | h
        · exact hjk h
        · exact hj (Finset.mem_of_mem_erase h)
      simp [hx, hx', hw, coordF_not_mem D _ hj, coordF_not_mem D' _ hj', hjk]
  · have e1 : ∑ j, ((x' j - x j) - t * w j) • augCol A j =
        (∑ j, x' j • augCol A j) - (∑ j, x j • augCol A j) -
          t • ((∑ j, (if j = k then (1:ℝ) else 0) • augCol A j) -
            ∑ j, coordF D (augCol A k) j • augCol A j) := by
      simp only [hw, sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
    rw [e1, hx, hx', sum_coordF, sum_coordF, sum_coordF]
    simp
  -- now: x' - x = t w
  have hxk : x k = 0 := coordF_not_mem D v hk
  have hlk' : l ≠ k := fun h => hk (h ▸ hl)
  have hl' : l ∉ D'.B := by rw [hB]; simp [hlk']
  have hzl := hz l
  simp only [hw, if_neg hlk', ← habar] at hzl
  have hx'l : x' l = 0 := coordF_not_mem D' v hl'
  rw [hx'l] at hzl
  -- 0 - x l - t * (0 - abar) = 0  => t = x l / abar
  have htv : t = x l / D.abar l k := by
    field_simp
    linarith
  -- sums
  have s1 : ∑ i ∈ D'.B, extCost c i * x' i = ∑ i, extCost c i * x' i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj; simp [hx', coordF_not_mem D' v hj]
  have s2 : ∑ i ∈ D.B, extCost c i * x i = ∑ i, extCost c i * x i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj; simp [hx, coordF_not_mem D v hj]
  have s3 : ∑ i ∈ D.B, extCost c i * D.abar i k = ∑ i, extCost c i * coordF D (augCol A k) i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj; simp [Dictionary.abar, hj]
  have hdiff : ∀ i, x' i = x i + t * w i := by
    intro i; have := hz i; linarith
  rw [s1, s2]
  simp_rw [hdiff, mul_add, Finset.sum_add_distrib]
  congr 1
  have : ∑ i, extCost c i * (t * w i) = t * D.cbar c k := by
    unfold Dictionary.cbar
    rw [s3, mul_sub, Finset.mul_sum]
    simp only [hw, mul_sub, Finset.sum_sub_distrib]
    congr 1
    · simp; ring
    · apply Finset.sum_congr rfl; intro i _; ring
  rw [this, htv]
  ring

/-- the stacked vectors whose coordinates give `lexRow`. -/
noncomputable def vecs (D₀ : Dictionary A) (b : Fin m → ℝ) : Fin (m + 1) → (Fin m → ℝ) :=
  Fin.cons b (fun p => augCol A (Dictionary.epsVar D₀ p))

lemma lexRow_eq (D₀ D : Dictionary A) (b : Fin m → ℝ) (i : Fin (n + m)) (q : Fin (m + 1)) :
    Dictionary.lexRow D₀ D b i q = coordF D (vecs D₀ b q) i := by
  refine Fin.cases ?_ ?_ q
  · simp [Dictionary.lexRow, vecs, Dictionary.bbar, coordF]
  · intro p
    simp [Dictionary.lexRow, vecs, Dictionary.abar, coordF]

end VanderbeiLP.Simplex.LexObj4697

theorem solution
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (D₀ D D' : VanderbeiLP.Simplex.Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hpos : ∀ i ∈ D.B, toLex (0 : Fin (m + 1) → ℝ) <
      toLex (VanderbeiLP.Simplex.Dictionary.lexRow D₀ D b i))
    (hpivot : VanderbeiLP.Simplex.Dictionary.IsLexPivot D₀ b c D D') :
    toLex (∑ i ∈ D.B, VanderbeiLP.Simplex.extCost c i •
      VanderbeiLP.Simplex.Dictionary.lexRow D₀ D b i) <
    toLex (∑ i ∈ D'.B, VanderbeiLP.Simplex.extCost c i •
      VanderbeiLP.Simplex.Dictionary.lexRow D₀ D' b i) := by
  obtain ⟨k, l, ⟨hk, hck⟩, ⟨hl, hlk, -⟩, hB⟩ := hpivot
  set r : ℝ := D.cbar c k / D.abar l k with hr
  have hrpos : 0 < r := div_pos hck hlk
  have hid : (∑ i ∈ D'.B, VanderbeiLP.Simplex.extCost c i •
      VanderbeiLP.Simplex.Dictionary.lexRow D₀ D' b i) =
      (∑ i ∈ D.B, VanderbeiLP.Simplex.extCost c i •
      VanderbeiLP.Simplex.Dictionary.lexRow D₀ D b i) +
      r • VanderbeiLP.Simplex.Dictionary.lexRow D₀ D b l := by
    funext q
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, VanderbeiLP.Simplex.LexObj4697.lexRow_eq]
    exact VanderbeiLP.Simplex.LexObj4697.exchange D D' c k l hk hl hlk.ne' hB
      (VanderbeiLP.Simplex.LexObj4697.vecs D₀ b q)
  rw [hid]
  obtain ⟨i, hi1, hi2⟩ := hpos l hl
  refine ⟨i, fun j hj => ?_, ?_⟩
  · have := hi1 j hj
    have h0 : VanderbeiLP.Simplex.Dictionary.lexRow D₀ D b l j = 0 := this.symm
    simp [h0]
  · have h2 : (0:ℝ) < VanderbeiLP.Simplex.Dictionary.lexRow D₀ D b l i := hi2
    simp only [Pi.toLex_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_pos hrpos h2]
