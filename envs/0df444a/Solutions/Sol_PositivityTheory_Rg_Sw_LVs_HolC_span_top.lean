-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.HolC.span_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:31.991433+00:00
-- url     : https://prove2.me/submissions/ce7ba058-bcb6-40a2-8013-35bc760719c8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_HermRealSmul
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology Set Metric Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.HolC
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.HolB
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.HolC
theorem _root_.solution (W : Submodule ℂ (M2 n))
    (hu : ∀ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b → (fromBlocks 0 b 0 0 : M2 n) ∈ W)
    (hl : ∀ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c → (fromBlocks 0 0 c 0 : M2 n) ∈ W)
    (hbr : ∀ b c : Matrix (Fin n) (Fin n) ℂ, bᴴ = b → cᴴ = c → (fromBlocks (-(b * c)) 0 0 (c * b) : M2 n) ∈ W)
    (h1 : (1 : M2 n) ∈ W) : W = ⊤ := by

  have dec : ∀ B : Matrix (Fin n) (Fin n) ℂ, ∃ b₁ b₂ : Matrix (Fin n) (Fin n) ℂ, b₁ᴴ = b₁ ∧ b₂ᴴ = b₂ ∧
      B = b₁ + Complex.I • b₂ := by
    intro B
    have hI : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      rw [mul_neg, mul_div_assoc', Complex.I_mul_I]; norm_num
    refine ⟨(1 / 2 : ℂ) • (B + Bᴴ), (-(Complex.I / 2)) • (B - Bᴴ), ?_, ?_, ?_⟩
    · rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
      congr 1
      simp [Complex.ext_iff]
    · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
      rw [show (Bᴴ - B) = -(B - Bᴴ) by abel, smul_neg, ← neg_smul]
      congr 1
      simp [Complex.ext_iff]
      norm_num
    · rw [smul_smul, hI]
      module
  have hU : ∀ B, (fromBlocks 0 B 0 0 : M2 n) ∈ W := by
    intro B
    obtain ⟨b₁, b₂, h₁, h₂, rfl⟩ := dec B
    have : (fromBlocks 0 (b₁ + Complex.I • b₂) 0 0 : M2 n) =
        fromBlocks 0 b₁ 0 0 + Complex.I • fromBlocks 0 b₂ 0 0 := by
      simp [fromBlocks_smul, fromBlocks_add]
    rw [this]
    exact W.add_mem (hu b₁ h₁) (W.smul_mem _ (hu b₂ h₂))
  have hL : ∀ C, (fromBlocks 0 0 C 0 : M2 n) ∈ W := by
    intro C
    obtain ⟨c₁, c₂, h₁, h₂, rfl⟩ := dec C
    have : (fromBlocks 0 0 (c₁ + Complex.I • c₂) 0 : M2 n) =
        fromBlocks 0 0 c₁ 0 + Complex.I • fromBlocks 0 0 c₂ 0 := by
      simp [fromBlocks_smul, fromBlocks_add]
    rw [this]
    exact W.add_mem (hl c₁ h₁) (W.smul_mem _ (hl c₂ h₂))
  have hBr : ∀ B C : Matrix (Fin n) (Fin n) ℂ, (fromBlocks (-(B * C)) 0 0 (C * B) : M2 n) ∈ W := by
    intro B C
    obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := dec B
    obtain ⟨c₁, c₂, hc₁, hc₂, rfl⟩ := dec C
    have e : (fromBlocks (-((b₁ + Complex.I • b₂) * (c₁ + Complex.I • c₂))) 0 0
        ((c₁ + Complex.I • c₂) * (b₁ + Complex.I • b₂)) : M2 n) =
        fromBlocks (-(b₁ * c₁)) 0 0 (c₁ * b₁) + Complex.I • fromBlocks (-(b₁ * c₂)) 0 0 (c₂ * b₁) +
          Complex.I • fromBlocks (-(b₂ * c₁)) 0 0 (c₁ * b₂) + (-1 : ℂ) • fromBlocks (-(b₂ * c₂)) 0 0 (c₂ * b₂) := by
      simp only [fromBlocks_smul, fromBlocks_add, smul_zero, add_zero]
      congr 1
      · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
        match_scalars <;> first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq
      · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
        match_scalars <;> first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq
    rw [e]
    exact W.add_mem (W.add_mem (W.add_mem (hbr _ _ hb₁ hc₁) (W.smul_mem _ (hbr _ _ hb₁ hc₂)))
      (W.smul_mem _ (hbr _ _ hb₂ hc₁))) (W.smul_mem _ (hbr _ _ hb₂ hc₂))

  let ιA : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n :=
    { toFun := fun A => fromBlocks A 0 0 0
      map_add' := fun A B => by simp [fromBlocks_add]
      map_smul' := fun c A => by simp [fromBlocks_smul] }
  let ιD : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n :=
    { toFun := fun D => fromBlocks 0 0 0 D
      map_add' := fun A B => by simp [fromBlocks_add]
      map_smul' := fun c A => by simp [fromBlocks_smul] }
  have sgl : ∀ (a b : Fin n) (c : ℂ), Matrix.single a b c = c • Matrix.single a b (1 : ℂ) := by
    intro a b c; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have offA : ∀ a b : Fin n, a ≠ b → ιA (Matrix.single a b 1) ∈ W := by
    intro a b hab
    have h := hBr (Matrix.single a b 1) (Matrix.single b b 1)
    rw [Matrix.single_mul_single_of_ne (h := Ne.symm hab), Matrix.single_mul_single_same, mul_one] at h
    have : ιA (Matrix.single a b 1) = -(fromBlocks (-(Matrix.single a b (1 : ℂ))) 0 0 0 : M2 n) := by
      simp [ιA, fromBlocks_neg]
    rw [this]; exact W.neg_mem h
  have offD : ∀ a b : Fin n, a ≠ b → ιD (Matrix.single a b 1) ∈ W := by
    intro a b hab
    have h := hBr (Matrix.single b b 1) (Matrix.single a b 1)
    rw [Matrix.single_mul_single_of_ne (h := Ne.symm hab), Matrix.single_mul_single_same, mul_one] at h
    simpa [ιD] using h
  have dif : ∀ a k : Fin n, ιD (Matrix.single k k 1) - ιA (Matrix.single a a 1) ∈ W := by
    intro a k
    have h := hBr (Matrix.single a k 1) (Matrix.single k a 1)
    rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_one] at h
    have : ιD (Matrix.single k k 1) - ιA (Matrix.single a a 1) =
        (fromBlocks (-(Matrix.single a a (1 : ℂ))) 0 0 (Matrix.single k k 1) : M2 n) := by
      simp [ιA, ιD, sub_eq_add_neg, fromBlocks_add, fromBlocks_neg]
    rw [this]; exact h
  have one_sum : (∑ a : Fin n, Matrix.single a a (1 : ℂ)) = 1 := by
    ext i j
    rw [Matrix.sum_apply]
    by_cases h : i = j
    · subst h; simp [Matrix.single_apply]
    · simp [Matrix.single_apply, Matrix.one_apply, h]
  have hST : ∑ a, ιA (Matrix.single a a 1) + ∑ k, ιD (Matrix.single k k 1) ∈ W := by
    rw [← map_sum, ← map_sum, one_sum]
    have : ιA 1 + ιD 1 = (1 : M2 n) := by simp [ιA, ιD, fromBlocks_add, ← fromBlocks_one]
    rw [this]; exact h1
  have hTS : ∑ k, ιD (Matrix.single k k 1) - ∑ a, ιA (Matrix.single a a 1) ∈ W := by
    rw [← Finset.sum_sub_distrib]
    exact W.sum_mem fun k _ => dif k k
  have hT : ∑ k, ιD (Matrix.single k k 1) ∈ W := by
    have h2 := W.add_mem hST hTS
    have : ∑ k, ιD (Matrix.single k k 1) = (1 / 2 : ℂ) • ((∑ a, ιA (Matrix.single a a 1) +
        ∑ k, ιD (Matrix.single k k 1)) + (∑ k, ιD (Matrix.single k k 1) - ∑ a, ιA (Matrix.single a a 1))) := by
      module
    rw [this]; exact W.smul_mem _ h2
  have hS : ∑ a, ιA (Matrix.single a a 1) ∈ W := by
    have := W.sub_mem hST hT
    simpa using this
  have diagA : ∀ a : Fin n, ιA (Matrix.single a a 1) ∈ W := by
    intro a
    have hn : (Fintype.card (Fin n) : ℂ) ≠ 0 := by
      simp only [Fintype.card_fin, ne_eq, Nat.cast_eq_zero]; exact Fin.pos a |>.ne'
    have hdiff : ∀ b : Fin n, ιA (Matrix.single a a 1) - ιA (Matrix.single b b 1) ∈ W := by
      intro b
      have := W.sub_mem (dif b a) (dif a a)
      have e : ιD (Matrix.single a a 1) - ιA (Matrix.single b b 1) - (ιD (Matrix.single a a 1) -
          ιA (Matrix.single a a 1)) = ιA (Matrix.single a a 1) - ιA (Matrix.single b b 1) := by abel
      rwa [e] at this
    have hsum := W.add_mem (W.sum_mem fun b (_ : b ∈ Finset.univ) => hdiff b) hS
    have e : ∑ b, (ιA (Matrix.single a a 1) - ιA (Matrix.single b b 1)) + ∑ a, ιA (Matrix.single a a 1) =
        (Fintype.card (Fin n) : ℂ) • ιA (Matrix.single a a 1) := by
      rw [Finset.sum_sub_distrib, sub_add_cancel, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [e] at hsum
    have := W.smul_mem ((Fintype.card (Fin n) : ℂ)⁻¹) hsum
    rwa [smul_smul, inv_mul_cancel₀ hn, one_smul] at this
  have diagD : ∀ k : Fin n, ιD (Matrix.single k k 1) ∈ W := by
    intro k
    have := W.add_mem (dif k k) (diagA k)
    simpa using this
  have allA : ∀ A : Matrix (Fin n) (Fin n) ℂ, ιA A ∈ W := by
    intro A
    rw [Matrix.matrix_eq_sum_single A, map_sum]
    refine W.sum_mem fun i _ => ?_
    rw [map_sum]
    refine W.sum_mem fun j _ => ?_
    rw [sgl, map_smul]
    refine W.smul_mem _ ?_
    by_cases hij : i = j
    · subst hij; exact diagA i
    · exact offA i j hij
  have allD : ∀ D : Matrix (Fin n) (Fin n) ℂ, ιD D ∈ W := by
    intro D
    rw [Matrix.matrix_eq_sum_single D, map_sum]
    refine W.sum_mem fun i _ => ?_
    rw [map_sum]
    refine W.sum_mem fun j _ => ?_
    rw [sgl, map_smul]
    refine W.smul_mem _ ?_
    by_cases hij : i = j
    · subst hij; exact diagD i
    · exact offD i j hij
  rw [eq_top_iff]
  intro M _
  rw [← Matrix.fromBlocks_toBlocks M]
  have e : (fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ : M2 n) =
      ιA M.toBlocks₁₁ + fromBlocks 0 M.toBlocks₁₂ 0 0 + fromBlocks 0 0 M.toBlocks₂₁ 0 + ιD M.toBlocks₂₂ := by
    simp [ιA, ιD, fromBlocks_add]
  rw [e]
  exact W.add_mem (W.add_mem (W.add_mem (allA _) (hU _)) (hL _)) (allD _)
end PositivityTheory.Rg.Sw.LVs.HolC
