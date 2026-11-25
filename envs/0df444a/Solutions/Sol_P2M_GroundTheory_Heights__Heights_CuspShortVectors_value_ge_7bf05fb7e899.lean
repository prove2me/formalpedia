-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CuspShortVectors_value_ge_7bf05fb7e899
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:41.48684+00:00
-- url     : https://prove2.me/submissions/2da5c64b-77b3-4f3b-af9f-5d23bdd722fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspShortVectors
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspShortVectors_intVec_eq_d2880f61d088
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspShortVectors_one_le_sq_of_ne_zero_08bad7f8c873
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_qf_nonneg_d6a602480fda
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_sq_le_inv_diag_mul_qf_f52478982262


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
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.CuspShortVectors
namespace GroundTheory.Heights₂.Heights.CuspShortVectors
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (hY : (τ.map Complex.im).PosDef)
    {c M : ℝ} (hM : 0 < M)
    (hcY : ∀ x : Fin g → ℝ, c * ∑ k, x k ^ 2 ≤ MCSchur.qf (τ.map Complex.im) x)
    (hPH : PeriodHermValue.Statement) (r : ℕ)
    (hdiag : ∀ k : Fin g, r ≤ k.val → (τ.map Complex.im) k k ≤ M) (a n : Fin g → ℤ)
    (h : n ≠ 0 ∨ ∃ k : Fin g, r ≤ k.val ∧ a k ≠ 0) :
    min c (1 / M) ≤ hermValue (τ.map Complex.im)⁻¹ (intVecC a + τ *ᵥ intVecC n) := by
  have hu : IsUnit (τ.map Complex.im).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit
  rw [intVec_eq, hPH g τ hu]
  have h1 := MCCusp.qf_nonneg hY.inv.posSemidef
    ((fun k => (a k : ℝ)) + τ.map Complex.re *ᵥ fun k => (n k : ℝ))
  have h2 := MCCusp.qf_nonneg hY.posSemidef fun k => (n k : ℝ)
  by_cases hn : n = 0
  · rcases h with h | ⟨k, hk, hak⟩
    · exact absurd hn h
    have hβ : (fun k => (n k : ℝ)) = 0 := by funext k; simp [hn]
    rw [hβ, mulVec_zero, add_zero]
    have hq0 : MCSchur.qf (τ.map Complex.im) 0 = 0 := by simp [MCSchur.qf]
    rw [hq0, add_zero]
    have hsq := MCCusp.sq_le_inv_diag_mul_qf hY.inv (fun k => (a k : ℝ)) k
    rw [Matrix.nonsing_inv_nonsing_inv _ hu] at hsq
    have ha := one_le_sq_of_ne_zero hak
    have hpos : 0 < (τ.map Complex.im) k k := hY.diag_pos
    have hle := hdiag k hk
    have hq := MCCusp.qf_nonneg hY.inv.posSemidef fun k => (a k : ℝ)
    have hM' : 1 / M ≤ MCSchur.qf (τ.map Complex.im)⁻¹ fun k => (a k : ℝ) := by
      rw [div_le_iff₀ hM]
      nlinarith
    exact (min_le_right _ _).trans hM'
  · obtain ⟨k, hk⟩ := Function.ne_iff.mp hn
    have hb := one_le_sq_of_ne_zero hk
    have hs := hcY fun k => (n k : ℝ)
    have hsum : ((n k : ℤ) : ℝ) ^ 2 ≤ ∑ j, ((n j : ℤ) : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun j => ((n j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ k)
    have hc : c ≤ MCSchur.qf (τ.map Complex.im) fun k => (n k : ℝ) := by
      rcases le_or_gt c 0 with hc0 | hc0
      · linarith
      · nlinarith
    linarith [min_le_left c (1 / M)]
end GroundTheory.Heights₂.Heights.CuspShortVectors
