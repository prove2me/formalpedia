-- Prove2me | solution 1 for PositivityTheory.ThKCT.Fr.IsFr.stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:23:50.658162+00:00
-- url     : https://prove2.me/submissions/c2a5bb29-9e19-4b44-a9d2-711a84fd791c

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
section
set_option linter.unusedSectionVars false
namespace PositivityTheory.ThKCT.Fr
open Matrix
variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {ε : R} {A' : Matrix (e ⊕ Fin 2) d R} {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}
private theorem fr_mulVec_sum_elim (u : e → R) (s t : R) :
    fr ι x y *ᵥ Sum.elim u ![s, t] = ι *ᵥ u + s • x + t • y := by
  ext i
  simp [fr, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] <;> ring
private theorem eq_of_iota_mulVec_add_smul_eq (h : IsFr c ε J J₁ ι x y A') {u u' : e → R} {s t s' t' : R}
    (e1 : ι *ᵥ u + s • x + t • y = ι *ᵥ u' + s' • x + t' • y) : u = u' ∧ s = s' ∧ t = t' := by
  rw [← fr_mulVec_sum_elim, ← fr_mulVec_sum_elim] at e1
  have h2 := congrArg (fun v => A' *ᵥ v) e1
  simp only [Matrix.mulVec_mulVec, h.inv2, Matrix.one_mulVec] at h2
  exact ⟨funext fun j => by simpa using congrFun h2 (Sum.inl j), by simpa using congrFun h2 (Sum.inr 0),
    by simpa using congrFun h2 (Sum.inr 1)⟩
private theorem mul_fr_eq_fr_mul_fromBlocks_and_preserves_gr (h : IsFr c ε J J₁ ι x y A') {p : Matrix d d R} (hp : pᵀ * J * p.map c = J) :
    p * fr ι x y = fr ι x y * Matrix.fromBlocks (A' * p * fr ι x y).toBlocks₁₁ (A' * p * fr ι x y).toBlocks₁₂
      (A' * p * fr ι x y).toBlocks₂₁ (A' * p * fr ι x y).toBlocks₂₂ ∧
    (A' * p * fr ι x y)ᵀ * gr ε J₁ * (A' * p * fr ι x y).map c = gr ε J₁ := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.fromBlocks_toBlocks, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.inv1, Matrix.one_mul]
  · calc (A' * p * fr ι x y)ᵀ * gr ε J₁ * (A' * p * fr ι x y).map c
        = (fr ι x y)ᵀ * (pᵀ * ((fr ι x y * A')ᵀ * J * (fr ι x y * A').map c) * p.map c) *
            (fr ι x y).map c := by
          rw [← h.gram]
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = gr ε J₁ := by
          rw [h.inv1, Matrix.transpose_one, Matrix.map_one _ c.map_zero c.map_one, Matrix.one_mul,
            Matrix.mul_one, hp, h.gram]
end PositivityTheory.ThKCT.Fr
end

set_option autoImplicit false
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Fr
open Matrix
variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {ε : R} {A' : Matrix (e ⊕ Fin 2) d R} {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}
namespace PositivityTheory.ThKCT.Fr
namespace IsFr
theorem _root_.solution (h : IsFr c ε J J₁ ι x y A') {t t' : R} (ht : t * t' = 1) {p : Matrix d d R}
    (hp : pᵀ * J * p.map c = J) (hx : p *ᵥ x = t • x) :
    ∃ (g : Matrix e e R) (α : e → R), g = (A' * p * fr ι x y).toBlocks₁₁ ∧ gᵀ * J₁ * g.map c = J₁ ∧ ∀ z, p *ᵥ (ι *ᵥ z) = ι *ᵥ (g *ᵥ z) + (α ⬝ᵥ z) • x := by
  have hct : c t * c t' = 1 := by rw [← map_mul, ht, map_one]
  obtain ⟨hpf, hQ⟩ := mul_fr_eq_fr_mul_fromBlocks_and_preserves_gr h hp
  have hQ' := hQ
  rw [← Matrix.fromBlocks_toBlocks (A' * p * fr ι x y)] at hQ'
  generalize (A' * p * fr ι x y).toBlocks₁₁ = g0 at hpf hQ' ⊢
  generalize (A' * p * fr ι x y).toBlocks₁₂ = b0 at hpf hQ' ⊢
  generalize (A' * p * fr ι x y).toBlocks₂₁ = a0 at hpf hQ' ⊢
  generalize (A' * p * fr ι x y).toBlocks₂₂ = s0 at hpf hQ' ⊢
  obtain ⟨c1, c2, c3⟩ := cols_of_mul hpf
  obtain ⟨hb0, hs00, hs10⟩ := eq_of_iota_mulVec_add_smul_eq h (u := 0) (s := t) (t := 0) (u' := fun j => b0 j 0)
    (s' := s0 0 0) (t' := s0 1 0) (by rw [← c2, hx]; simp)
  have hb0' : ∀ j, b0 j 0 = 0 := fun j => (congrFun hb0 j).symm
  unfold gr at hQ'
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hQ'
  obtain ⟨e11, e12, -, -⟩ := hQ'
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e11 e12
  have ha1 : ∀ i, a0 1 i = 0 := by
    intro i
    have h12 := congrFun (congrFun e12 i) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, hb0', ← hs00, ← hs10] at h12
    linear_combination (ε * c t') * h12 - a0 1 i * h.eps - a0 1 i * ε * ε * hct
  have haK : a0ᵀ * !![0, 1; ε, 0] * a0.map c = 0 := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha1]
  rw [haK, add_zero] at e11
  refine ⟨g0, fun j => a0 0 j, rfl, e11, fun z => ?_⟩
  rw [Matrix.mulVec_mulVec, c1, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha1] <;> ring
end IsFr
end PositivityTheory.ThKCT.Fr
