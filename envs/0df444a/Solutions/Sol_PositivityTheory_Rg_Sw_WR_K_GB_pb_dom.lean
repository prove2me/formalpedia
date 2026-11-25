-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:08:23.065519+00:00
-- url     : https://prove2.me/submissions/d71b0039-6b1f-400f-831e-2caa5b1d3f75

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_norm_one_sub
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pbwt_pos
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pbwt_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (a : ℂ) (ha : a = Complex.I ∨ a = -Complex.I) (lam : Fin n → ℝ) (c₀ : ℝ) (hc : 0 ≤ c₀)
    (hc₀ : (n : ℝ) * c₀ ≤ 1 / 4) (b : Mc n)
    (hb : ∀ i j, ‖b i j - Matrix.diagonal (fun i => (lam i : ℂ)) i j‖ ≤ c₀ * (pbwt lam i * pbwt lam j))
    (x : Fin n → ℂ) (B : ℝ) (hy : ∀ i, ‖((1 - a • b) *ᵥ x) i‖ ≤ B * pbwt lam i) :
    ∀ i, pbwt lam i * ‖x i‖ ≤ 3 * B := by
  intro i
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun j => pbwt lam j * ‖x j‖) ⟨i, Finset.mem_univ _⟩
  set m := pbwt lam i0 * ‖x i0‖ with hmdef
  have hm : ∀ j, pbwt lam j * ‖x j‖ ≤ m := fun j => hi0 j (Finset.mem_univ _)
  have hm0 : 0 ≤ m := mul_nonneg (pbwt_pos lam i0).le (norm_nonneg _)
  have ha1 : ‖a‖ = 1 := by rcases ha with rfl | rfl <;> simp
  have hD : ∑ j, Matrix.diagonal (fun i => (lam i : ℂ)) i0 j * x j = (lam i0 : ℂ) * x i0 := by
    rw [Finset.sum_eq_single i0]
    · simp [Matrix.diagonal_apply_eq]
    · intro j _ hj; simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
    · simp
  have row : ((1 - a • b) *ᵥ x) i0 = (1 - a * (lam i0 : ℂ)) * x i0 -
      a * ∑ j, (b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j) * x j := by
    have e1 : ((1 - a • b) *ᵥ x) i0 = x i0 - a * ∑ j, b i0 j * x j := by
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_mul,
        Finset.sum_sub_distrib, Finset.mul_sum, Matrix.one_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_assoc]
    rw [e1]; simp only [sub_mul, Finset.sum_sub_distrib, hD]; ring
  have hsum : ‖∑ j, (b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j) * x j‖ ≤ (n : ℝ) * (c₀ * pbwt lam i0 * m) := by
    calc ‖∑ j, (b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j) * x j‖ ≤ ∑ j, ‖(b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j) * x j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, c₀ * pbwt lam i0 * m := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul]
        calc ‖(b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j)‖ * ‖x j‖ ≤ (c₀ * (pbwt lam i0 * pbwt lam j)) * ‖x j‖ :=
              mul_le_mul_of_nonneg_right (hb i0 j) (norm_nonneg _)
          _ = c₀ * pbwt lam i0 * (pbwt lam j * ‖x j‖) := by ring
          _ ≤ c₀ * pbwt lam i0 * m :=
              mul_le_mul_of_nonneg_left (hm j) (mul_nonneg hc (pbwt_pos lam i0).le)
      _ = (n : ℝ) * (c₀ * pbwt lam i0 * m) := by simp
  have hlow : (pbwt lam i0 / Real.sqrt 2) * m ≤ ‖(1 - a * (lam i0 : ℂ)) * x i0‖ := by
    rw [norm_mul]
    have h1 := pb_norm_one_sub a ha (lam i0)
    have : (pbwt lam i0 / Real.sqrt 2) * m = ((1 + |lam i0|) / Real.sqrt 2) * ‖x i0‖ := by
      rw [hmdef, ← pbwt_sq]; ring
    rw [this]; exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hup : ‖(1 - a * (lam i0 : ℂ)) * x i0‖ ≤ B * pbwt lam i0 + (n : ℝ) * (c₀ * pbwt lam i0 * m) := by
    have e : (1 - a * (lam i0 : ℂ)) * x i0 = ((1 - a • b) *ᵥ x) i0 + a * ∑ j, (b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j) * x j := by
      rw [row]; ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add (hy i0) ?_)
    rw [norm_mul, ha1, one_mul]; exact hsum
  have key : pbwt lam i0 * (m / Real.sqrt 2) ≤ pbwt lam i0 * (B + (n : ℝ) * c₀ * m) := by
    have := hlow.trans hup
    calc pbwt lam i0 * (m / Real.sqrt 2) = (pbwt lam i0 / Real.sqrt 2) * m := by ring
      _ ≤ B * pbwt lam i0 + (n : ℝ) * (c₀ * pbwt lam i0 * m) := this
      _ = pbwt lam i0 * (B + (n : ℝ) * c₀ * m) := by ring
  have key2 := le_of_mul_le_mul_left key (pbwt_pos lam i0)
  have hs2 : Real.sqrt 2 ≤ 10 / 7 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hsp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hmd : m * (7 / 10) ≤ m / Real.sqrt 2 := by
    rw [le_div_iff₀ hsp]; nlinarith
  have hnc : (n : ℝ) * c₀ * m ≤ m / 4 := by nlinarith
  have hfin : m ≤ 3 * B := by nlinarith
  exact (hm i).trans hfin
end PositivityTheory.Rg.Sw.WR.K.GB
