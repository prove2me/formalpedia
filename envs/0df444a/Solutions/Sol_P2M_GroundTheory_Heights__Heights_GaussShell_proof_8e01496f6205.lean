-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussShell_proof_8e01496f6205
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:06.134041+00:00
-- url     : https://prove2.me/submissions/cf133bd2-2842-408a-8b73-1eac27c32e90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussShell
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PGaussShell_base_le_74f8b6676cc1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Real
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace GaussShell
theorem _root_.solution (hP : GaussPacking.Statement) (hT : GaussTermBound.Statement) :
    GaussShell.Statement := by
  intro n hn Λ δ hδ hmin F m
  set T := F.filter (fun μ : Λ => ⌊‖(μ : EuclideanSpace ℝ (Fin n))‖⌋₊ = m) with hTdef
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hlow : ∀ μ ∈ T, (m : ℝ) ≤ ‖(μ : EuclideanSpace ℝ (Fin n))‖ := by
    intro μ hμ
    rw [← (Finset.mem_filter.1 hμ).2]
    exact Nat.floor_le (norm_nonneg _)
  have hup : ∀ μ ∈ T, ‖(μ : EuclideanSpace ℝ (Fin n))‖ ≤ (m : ℝ) + 1 := by
    intro μ hμ
    have h := Nat.lt_floor_add_one ‖(μ : EuclideanSpace ℝ (Fin n))‖
    rw [(Finset.mem_filter.1 hμ).2] at h
    exact h.le
  have hterm : ∀ μ ∈ T, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
      Real.exp (-π * (m : ℝ) ^ 2) := by
    intro μ hμ
    apply Real.exp_le_exp.2
    have : (m : ℝ) ^ 2 ≤ ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
      pow_le_pow_left₀ hm0 (hlow μ hμ) 2
    nlinarith [Real.pi_pos]
  have hsum : ∑ μ ∈ T, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2) ≤
      (T.card : ℝ) * Real.exp (-π * (m : ℝ) ^ 2) := by
    have h := Finset.sum_le_sum hterm
    rwa [Finset.sum_const, nsmul_eq_mul] at h
  have hcard : (T.card : ℝ) ≤ (1 + 2 * ((m : ℝ) + 1) / δ) ^ n := by
    have h := hP n (T.map (Function.Embedding.subtype _)) δ ((m : ℝ) + 1) hδ (by linarith) ?_ ?_
    · rwa [Finset.card_map] at h
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 hy
      simp only [Function.Embedding.coe_subtype] at hxy ⊢
      exact hmin _ (Λ.sub_mem a.2 b.2) (sub_ne_zero.2 hxy)
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
      exact hup a ha
  have hδ' : (0 : ℝ) ≤ 1 + 1 / δ := by
    have : 0 ≤ 1 / δ := le_of_lt (one_div_pos.2 hδ)
    linarith
  have hb0 : (0 : ℝ) ≤ 1 + 2 * ((m : ℝ) + 1) / δ := by
    have : 0 ≤ 2 * ((m : ℝ) + 1) / δ := div_nonneg (by linarith) hδ.le
    linarith
  have hpow : (1 + 2 * ((m : ℝ) + 1) / δ) ^ n ≤
      3 ^ n * ((m : ℝ) + 1) ^ n * (1 + 1 / δ) ^ n := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ hb0 (PGaussShell.base_le _ _ hm0 hδ) n
  calc ∑ μ ∈ T, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin n))‖ ^ 2)
      ≤ (T.card : ℝ) * Real.exp (-π * (m : ℝ) ^ 2) := hsum
    _ ≤ 3 ^ n * ((m : ℝ) + 1) ^ n * (1 + 1 / δ) ^ n * Real.exp (-π * (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right (hcard.trans hpow) (Real.exp_pos _).le
    _ = 3 ^ n * (1 + 1 / δ) ^ n * (((m : ℝ) + 1) ^ n * Real.exp (-π * (m : ℝ) ^ 2)) := by ring
    _ ≤ 3 ^ n * (1 + 1 / δ) ^ n * (√(n : ℝ) ^ n * Real.exp √(n : ℝ) *
          Real.exp (n / (2 * π)) * Real.exp (-(m : ℝ))) :=
        mul_le_mul_of_nonneg_left (hT n hn m) (by positivity)
    _ = gaussShellConst n * (1 + 1 / δ) ^ n * Real.exp (-(m : ℝ)) := by
        unfold gaussShellConst; ring
end GaussShell
end GroundTheory.Heights₂.Heights
