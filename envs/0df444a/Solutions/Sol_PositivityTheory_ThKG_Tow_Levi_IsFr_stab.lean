-- Prove2me | solution 1 for PositivityTheory.ThKG.Tow.Levi.IsFr.stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:23:24.430997+00:00
-- url     : https://prove2.me/submissions/f023640c-8a03-4187-beab-45526488e260

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
theorem _root_.solution (h : IsFr c J J₁ ι x y) {t t' : R} (ht : t * t' = 1) {p : Matrix d d R}
    (hp : pᵀ * J * p.map c = J) (hx : p *ᵥ x = t • x) :
    ∃ (g : Matrix e e R) (α : e → R), gᵀ * J₁ * g.map c = J₁ ∧ ∀ z, p *ᵥ (ι *ᵥ z) = ι *ᵥ (g *ᵥ z) + (α ⬝ᵥ z) • x := by
  obtain ⟨hG, A', h1, h2⟩ := h
  set A := fr ι x y with hA
  have hP : (A' * p * A)ᵀ * gr J₁ * (A' * p * A).map c = gr J₁ := by
    have e1 : A.map c * A'.map c = 1 := by
      rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← hG]
    calc _ = Aᵀ * (pᵀ * ((A * A')ᵀ * J * (A.map c * A'.map c)) * p.map c) * A.map c := by
          simp only [Matrix.map_mul, transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1, e1, transpose_one, Matrix.one_mul, Matrix.mul_one, hp]
  have e2 : p * A = A * (A' * p * A) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have e3 : ∀ i, (A' * p * A) i (Sum.inr 0) = t * (1 : Matrix (e ⊕ Fin 2) (e ⊕ Fin 2) R) i (Sum.inr 0) := fun i => by
    rw [← h2, Matrix.mul_assoc]
    change (A' *ᵥ (p *ᵥ x)) i = t * (A' *ᵥ x) i
    rw [hx, mulVec_smul]; rfl
  generalize A' * p * A = P at hP e2 e3
  have hct : c t * c t' = 1 := by rw [← map_mul, ht, map_one]
  have e4 : ∀ j, P (Sum.inr 1) (Sum.inl j) = 0 := fun j => by
    have := congrFun (congrFun hP (Sum.inl j)) (Sum.inr 0)
    simp [mul_apply, e3, gr, one_apply, Fintype.sum_sum_type, apply_ite c] at this
    calc _ = P (Sum.inr 1) (Sum.inl j) * c t * c t' := by rw [mul_assoc, hct, mul_one]
      _ = 0 := by rw [this, zero_mul]
  rw [← fromBlocks_toBlocks P] at e2
  refine ⟨P.toBlocks₁₁, fun j => P (Sum.inr 0) (Sum.inl j), ?_, fun z => ?_⟩
  · ext i j
    have := congrFun (congrFun hP (Sum.inl i)) (Sum.inl j)
    simpa [mul_apply, e4, gr, Fintype.sum_sum_type, toBlocks₁₁] using this
  · rw [mulVec_mulVec, (cols_of_mul e2).1, add_mulVec, mulVec_mulVec]
    congr 1
    ext i
    simp [mulVec, dotProduct, mul_apply, toBlocks₂₁, e4, Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm]
end IsFr
end PositivityTheory.ThKG.Tow.Levi
