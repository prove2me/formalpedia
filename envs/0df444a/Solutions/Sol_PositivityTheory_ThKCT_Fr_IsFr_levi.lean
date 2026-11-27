-- Prove2me | solution 1 for PositivityTheory.ThKCT.Fr.IsFr.levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:23:41.523332+00:00
-- url     : https://prove2.me/submissions/a0980c89-dbcf-4a4b-ae95-a38430e20974

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_ColsOfMul
import Theorems.Thm_PositivityTheory_ThKCT_Fr_cols_of_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Fr
open Matrix
variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {ε : R} {A' : Matrix (e ⊕ Fin 2) d R} {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}
namespace PositivityTheory.ThKCT.Fr
namespace IsFr
theorem _root_.solution (h : IsFr c ε J J₁ ι x y A') (hcc : ∀ a, c (c a) = a) {t t' : R} (ht : t * t' = 1) {g g' : Matrix e e R}
    (hg' : g * g' = 1) (hg : gᵀ * J₁ * g.map c = J₁) :
    ∃ m m' : Matrix d d R, m = fr ι x y * dg g t (c t') * A' ∧ m * m' = 1 ∧ mᵀ * J * m.map c = J ∧ m *ᵥ x = t • x ∧ m *ᵥ y = c t' • y ∧ m * ι = ι * g := by
  have hct : c t * c t' = 1 := by rw [← map_mul, ht, map_one]
  have hct' : c t' * c t = 1 := by rw [mul_comm]; exact hct
  have hdd : dg g t (c t') * dg g' t' (c t) = 1 := by
    unfold dg
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hg']
    rw [← Matrix.fromBlocks_one]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht, hct']
  have hdgT : (dg g t (c t'))ᵀ * gr ε J₁ * (dg g t (c t')).map c = gr ε J₁ := by
    unfold dg gr
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_zero, Matrix.map_zero _ c.map_zero, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add]
    rw [hg]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hcc, ht] <;>
      linear_combination ε * hct'
  have hmfr : fr ι x y * dg g t (c t') * A' * fr ι x y = fr ι x y * dg g t (c t') := by
    rw [Matrix.mul_assoc, h.inv2, Matrix.mul_one]
  obtain ⟨c1, c2, c3⟩ := cols_of_mul (g := g) (b := 0) (a := 0) (s := !![t, 0; 0, c t']) hmfr
  refine ⟨fr ι x y * dg g t (c t') * A', fr ι x y * dg g' t' (c t) * A', rfl, ?_, ?_, ?_, ?_, ?_⟩
  · calc fr ι x y * dg g t (c t') * A' * (fr ι x y * dg g' t' (c t) * A')
        = fr ι x y * (dg g t (c t') * (A' * fr ι x y) * dg g' t' (c t)) * A' := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h.inv2, Matrix.mul_one, hdd, Matrix.mul_one, h.inv1]
  · calc (fr ι x y * dg g t (c t') * A')ᵀ * J * (fr ι x y * dg g t (c t') * A').map c
        = A'ᵀ * ((dg g t (c t'))ᵀ * ((fr ι x y)ᵀ * J * (fr ι x y).map c) * (dg g t (c t')).map c) *
            A'.map c := by
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = A'ᵀ * ((fr ι x y)ᵀ * J * (fr ι x y).map c) * A'.map c := by rw [h.gram, hdgT]
      _ = (fr ι x y * A')ᵀ * J * (fr ι x y * A').map c := by
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = J := by
          rw [h.inv1, Matrix.transpose_one, Matrix.map_one _ c.map_zero c.map_one, Matrix.one_mul,
            Matrix.mul_one]
  · rw [c2]
    ext i
    simp [Matrix.mulVec, dotProduct]
  · rw [c3]
    ext i
    simp [Matrix.mulVec, dotProduct]
  · rw [c1]
    simp
end IsFr
end PositivityTheory.ThKCT.Fr
