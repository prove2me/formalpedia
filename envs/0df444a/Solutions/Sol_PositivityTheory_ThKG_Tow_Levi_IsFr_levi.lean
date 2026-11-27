-- Prove2me | solution 1 for PositivityTheory.ThKG.Tow.Levi.IsFr.levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:23:19.447143+00:00
-- url     : https://prove2.me/submissions/6566f5a2-a4a3-4d01-bb34-150544961c2b

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_TowerModels_LeviAlg
import Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_cols_of_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.ThKG.Tow.Levi
open Matrix
variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}
namespace PositivityTheory.ThKG.Tow.Levi
namespace IsFr
theorem _root_.solution (h : IsFr c J J₁ ι x y) (hcc : ∀ a, c (c a) = a) {t t' : R} (ht : t * t' = 1) {g g' : Matrix e e R}
    (hg' : g * g' = 1) (hg : gᵀ * J₁ * g.map c = J₁) :
    ∃ m m' : Matrix d d R, m * m' = 1 ∧ mᵀ * J * m.map c = J ∧ m *ᵥ x = t • x ∧ m *ᵥ y = c t' • y ∧ m * ι = ι * g := by
  obtain ⟨hG, A', h1, h2⟩ := h
  set A := fr ι x y with hA
  let D : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R := fromBlocks g 0 0 !![t, 0; 0, c t']
  let D' : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R := fromBlocks g' 0 0 !![t', 0; 0, c t]
  have hct : c t' * c t = 1 := by rw [← map_mul, mul_comm, ht, map_one]
  have hD : D * D' = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · simpa using hg'
    · simp
    · simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [ht, hct]
  have hDG : Dᵀ * gr J₁ * D.map c = gr J₁ := by
    rw [gr, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    congr 1
    · simpa using hg
    · simp
    · simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_apply, ht, hct, hcc]
  have e1 : A.map c * A'.map c = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : A * D * A' * A = A * D := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  obtain ⟨c1, c2, c3⟩ := cols_of_mul e2
  refine ⟨A * D * A', A * D' * A', ?_, ?_, ?_, ?_, ?_⟩
  · calc _ = A * (D * (A' * A) * D') * A' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, hD, Matrix.mul_one, h1]
  · calc _ = A'ᵀ * (Dᵀ * (Aᵀ * J * A.map c) * D.map c) * A'.map c := by
          simp only [Matrix.map_mul, transpose_mul, Matrix.mul_assoc]
      _ = (A * A')ᵀ * J * (A.map c * A'.map c) := by
          rw [hG, hDG, ← hG]; simp only [transpose_mul, Matrix.mul_assoc]
      _ = J := by rw [h1, e1, transpose_one, Matrix.one_mul, Matrix.mul_one]
  · rw [c2]; ext i; simp [mulVec, dotProduct]
  · rw [c3]; ext i; simp [mulVec, dotProduct]
  · simpa using c1
end IsFr
end PositivityTheory.ThKG.Tow.Levi
