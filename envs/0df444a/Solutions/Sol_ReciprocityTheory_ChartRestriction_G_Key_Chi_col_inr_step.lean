-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.col_inr_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:27:21.35265+00:00
-- url     : https://prove2.me/submissions/2d3d9596-b3b5-4338-9d62-ff268ee76153

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenFin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_colsFixed_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_colsFixed_spDiag_rk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_colsFixed_spTransl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_mul_col_of_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_rkU_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_row_inl_of_col_inr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_row_inr_of_col_inl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spDiag_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spDiag_rk_mul_inr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spH_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spTransl_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spTransl_mul_inl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spTransl_mul_inr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution (k : Fin g) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hM : M ∈ symplecticGroup (Fin g) ℤ) (hF : ColsFixed k M)
    (hk : ∀ r, M r (Sum.inl k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k)) :
    ∃ O ∈ spH g, ColsFixed k O ∧
      (∀ r, O r (Sum.inl k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k)) ∧
      ∀ r, (O * M) r (Sum.inr k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inr k) := by
  have hrow : ∀ q, M (Sum.inr k) q = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (Sum.inr k) q :=
    row_inr_of_col_inl hM hk
  have hck : M (Sum.inr k) (Sum.inr k) = 1 := by rw [hrow]; simp
  have hlow : ∀ i : Fin g, (i : ℕ) < k → M (Sum.inr i) (Sum.inr k) = 0 := by
    intro i hi
    have hik : i ≠ k := by intro h; subst h; omega
    rw [row_inr_of_col_inl hM (hF i hi).1]; simp [Matrix.one_apply, hik]
  set c' : Fin g → ℤ := fun l => if (k : ℕ) < l then M (Sum.inr l) (Sum.inr k) else 0 with hc'
  have hdot : c' ⬝ᵥ Pi.single k 1 = 0 := by rw [dotProduct_single]; simp [hc']
  have hDmem : spDiag (rkU _ _ hdot) ∈ spH g := spDiag_mem _
  have hDF : ColsFixed k (spDiag (rkU _ _ hdot)) := by
    refine colsFixed_spDiag_rk hdot (fun i hi => ?_) (fun i hi => ?_)
    · have hik : i ≠ k := by intro h; subst h; omega
      simp [Pi.single_apply, hik]
    · simp only [hc']
      rw [if_neg (by omega)]
  have hDk : ∀ r, spDiag (rkU _ _ hdot) r (Sum.inl k) =
      (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k) := by
    intro r
    rcases r with l | l
    · rw [spDiag, fromBlocks_apply₁₁, rkU_val]
      simp [vecMulVec_apply, hc', Matrix.one_apply]
    · simp [spDiag]
  set M1 := spDiag (rkU _ _ hdot) * M with hM1
  have hM1sp : M1 ∈ symplecticGroup (Fin g) ℤ :=
    (symplecticGroup (Fin g) ℤ).mul_mem (spH_le g hDmem) hM
  have hM1F : ColsFixed k M1 := colsFixed_mul hDF hF
  have hc1 : ∀ l, M1 (Sum.inr l) (Sum.inr k) =
      (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (Sum.inr l) (Sum.inr k) := by
    intro l
    rw [hM1, spDiag_rk_mul_inr]
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, hck, mul_one, hc']
    rcases lt_trichotomy (l : ℕ) k with h | h | h
    · have hlk : l ≠ k := by intro e; subst e; omega
      rw [if_neg (by omega), hlow l h]; simp [Matrix.one_apply, hlk]
    · have e : l = k := Fin.ext h
      subst e; rw [if_neg (lt_irrefl _), hck]; simp
    · have hlk : l ≠ k := by intro e; subst e; omega
      rw [if_pos h]; simp [Matrix.one_apply, hlk]
  have ha1 : ∀ i : Fin g, (i : ℕ) < k → M1 (Sum.inl i) (Sum.inr k) = 0 := by
    intro i hi
    rw [row_inl_of_col_inr hM1sp (hM1F i hi).2]; simp [Matrix.one_apply]
  set S : Matrix (Fin g) (Fin g) ℤ := Matrix.of fun l m =>
    if m = k then (if l = k then -M1 (Sum.inl k) (Sum.inr k) else -M1 (Sum.inl l) (Sum.inr k))
    else (if l = k then -M1 (Sum.inl m) (Sum.inr k) else 0) with hS
  have hSsym : S.IsSymm := by
    refine Matrix.IsSymm.ext (fun l m => ?_)
    simp only [hS, of_apply]
    by_cases hl : l = k <;> by_cases hm : m = k <;> simp [hl, hm]
  have hSmem : spTransl S ∈ spH g := spTransl_mem hSsym
  have hSF : ColsFixed k (spTransl S) := by
    refine colsFixed_spTransl (fun i hi l => ?_)
    have hik : i ≠ k := by intro h; subst h; omega
    simp [hS, hik, ha1 i hi]
  have hSk : ∀ r, spTransl S r (Sum.inl k) =
      (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k) := by
    intro r; rcases r with l | l <;> simp [spTransl, Matrix.one_apply]
  refine ⟨spTransl S * spDiag (rkU _ _ hdot), (spH g).mul_mem hSmem hDmem, colsFixed_mul hSF hDF,
    fun r => by rw [mul_col_of_unit hDk]; exact hSk r, ?_⟩
  intro r
  rw [Matrix.mul_assoc]
  show (spTransl S * M1) r (Sum.inr k) = _
  rcases r with l | l
  · rw [spTransl_mul_inl]
    have hsum : ∑ m, S l m * M1 (Sum.inr m) (Sum.inr k) = S l k := by
      simp only [hc1, Matrix.one_apply, Sum.inr.injEq, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hsum]
    simp only [hS, of_apply, if_true]
    by_cases hl : l = k
    · subst hl; simp
    · simp [hl]
  · rw [spTransl_mul_inr, hc1]
end ReciprocityTheory.ChartRestriction.G.Key.Chi
