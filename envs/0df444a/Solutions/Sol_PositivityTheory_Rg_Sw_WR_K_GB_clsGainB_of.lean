-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.clsGainB_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:18.634723+00:00
-- url     : https://prove2.me/submissions/00764270-2d2a-460a-9ea2-488da5ba33e1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_RatBound
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContDiffHerm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_contDiff_herm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_cls_nat
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_cls_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_dP_pos
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_herm_mem_Ugood
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_ratBound


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
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (hC : CauchyW) (hI : Invar) (hB : PBound) (hL : Link) (hT : Twist) (hLg : Lagr) : ClsGain := by
  intro n s hs p q N R
  obtain ⟨hUo, hFc, -⟩ := hB n s hs p q R
  have hH : ContDiff ℝ (⊤ : ℕ∞) (cls s 0 p q R) := by
    rw [cls_zero]
    rw [contDiff_iff_contDiffAt]
    intro y
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (Fr s p q R) (herm y) :=
      ((hFc.restrict_scalars ℝ).contDiffAt (hUo.mem_nhds (herm_mem_Ugood s hs y)))
    exact h1.comp y (contDiff_herm n).contDiffAt
  obtain ⟨G, hGc, hG⟩ := hT n (cls s 0 p q R) hH N
  have hcls : ∀ z : ℂ, cls s z p q R = fun y => ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y := by
    intro z; funext y; simp only [cls, neg_zero, Complex.cpow_zero, one_mul]; ring
  set D := n * N with hD
  have hrat : ∀ i : ℕ, ∃ C : ℝ, ∀ y : E n,
      ‖(Delta^[N] (cls s 0 (p + i) (q + i) R)) y‖ ≤ C * (dP y) ^ (-((p + i + (q + i) + N : ℕ) : ℝ) / 2) :=
    fun i => ratBound hC hI hB hL s hs (p + i) (q + i) N R
  choose Ci hCi using hrat
  obtain ⟨CL, hCL⟩ := hLg D
  set Cm : ℝ := ∑ i ∈ Finset.range (D + 1), |Ci i| with hCm
  refine ⟨D + 1, fun j => Polynomial.X ^ (j : ℕ), fun j => G j, fun j => (hGc j).continuous, ⟨CL * Cm, ?_⟩, ?_⟩
  · intro j y
    have hdp := dP_pos y
    have hval : ∀ i ≤ D, ‖∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * G j y‖ ≤ Cm * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
      intro i hi
      have e1 := hG (i : ℂ) y
      rw [← hcls, cls_nat s hs i p q R] at e1
      have hne : (((dP y : ℝ) : ℂ)) ^ (-(i : ℂ)) ≠ 0 := by
        rw [Complex.cpow_neg, Complex.cpow_natCast]; exact inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hdp.ne'))
      have e2 : ∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * G j y =
          (((dP y : ℝ) : ℂ)) ^ i * (Delta^[N] (cls s 0 (p + i) (q + i) R)) y := by
        rw [e1, Complex.cpow_neg, Complex.cpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hdp.ne')), one_mul]
      rw [e2, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hdp.le]
      have hb := hCi i y
      have hCi_le : |Ci i| ≤ Cm := by
        rw [hCm]
        exact Finset.single_le_sum (f := fun i => |Ci i|) (fun i _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
      calc dP y ^ i * ‖(Delta^[N] (cls s 0 (p + i) (q + i) R)) y‖
          ≤ dP y ^ i * (Ci i * (dP y) ^ (-((p + i + (q + i) + N : ℕ) : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hb (pow_nonneg hdp.le _)
        _ = Ci i * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
            rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add hdp]
            congr 2; push_cast; ring
        _ ≤ Cm * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCi_le) (Real.rpow_nonneg hdp.le _)
    have := hCL (fun j => G j y) _ hval j (Nat.lt_succ_iff.1 j.2)
    simpa [mul_assoc] using this
  · intro z y
    rw [hcls z, hG z y]
    congr 1
    rw [Finset.sum_range (fun j => z ^ j * G j y)]
    simp [Polynomial.eval_pow, Polynomial.eval_X]
end PositivityTheory.Rg.Sw.WR.K.GB
