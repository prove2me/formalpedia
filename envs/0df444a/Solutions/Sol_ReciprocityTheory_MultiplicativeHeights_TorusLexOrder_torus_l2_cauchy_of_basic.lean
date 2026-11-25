-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.torus_l2_cauchy_of_basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:17:35.777744+00:00
-- url     : https://prove2.me/submissions/0df6d481-d28a-4776-8fab-b9d802348656

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexB
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexC
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_torus_coeff_integral
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_torus_parseval
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_exists_torus_max
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_continuous_eval_torus
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_integrable_of_bdd
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_norm_eval_torus_le
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_norm_torusPoint
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_torusProb_isProb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
open MeasureTheory ComplexConjugate
private theorem norm_torusMono_eq_one {ι : Type} [Fintype ι] (θ : ι → ℝ) (s : ι →₀ ℕ) :
    ‖torusMono θ s‖ = 1 := by
  unfold torusMono
  rw [norm_prod]
  simp [norm_pow, norm_torusPoint]
end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
open MeasureTheory ComplexConjugate
namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
theorem _root_.solution (hBasic : TorusMeanBasicStatement) : TorusL2Cauchy := by
  intro ι _ f
  haveI := torusProb_isProb ι
  obtain ⟨hInt, hMul, hMono⟩ := hBasic ι
  constructor
  · intro hf
    set A := ∑ s ∈ f.support, ‖f.coeff s‖ ^ 2 with hA
    have hApos : 0 < A := by
      obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hf)
      exact Finset.sum_pos' (fun _ _ => by positivity)
        ⟨s, hs, pow_pos (norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp hs)) 2⟩
    have hq : 0 < Real.exp 1 / A := div_pos (Real.exp_pos 1) hApos
    set r : ℝ := Real.sqrt (Real.exp 1 / A) with hrdef
    have hr : 0 < r := Real.sqrt_pos.mpr hq
    have hr2 : r ^ 2 = Real.exp 1 / A := Real.sq_sqrt hq.le
    have hc : ((r : ℂ)) ≠ 0 := by exact_mod_cast hr.ne'
    have hcn : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
    have hCc : (MvPolynomial.C (r : ℂ) : MvPolynomial ι ℂ) ≠ 0 := by simpa using hc
    have hmean : torusMean (MvPolynomial.C (r : ℂ) * f) = Real.log r + torusMean f := by
      rw [hMul _ _ hCc hf, MvPolynomial.C_apply, hMono, hcn]
    have hpt : ∀ θ, Real.log ‖MvPolynomial.eval (torusPoint θ) (MvPolynomial.C (r : ℂ) * f)‖ ≤
        r ^ 2 / Real.exp 1 * ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 / 2 := by
      intro θ
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, norm_mul, hcn]
      have hx : 0 ≤ ‖MvPolynomial.eval (torusPoint θ) f‖ := norm_nonneg _
      rcases hx.eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have hy : 0 < (r * ‖MvPolynomial.eval (torusPoint θ) f‖) ^ 2 / Real.exp 1 := by positivity
        have h1 := Real.log_le_sub_one_of_pos hy
        rw [Real.log_div (ne_of_gt (by positivity)) (Real.exp_pos 1).ne', Real.log_exp,
          Real.log_pow] at h1
        have e2 : (r * ‖MvPolynomial.eval (torusPoint θ) f‖) ^ 2 / Real.exp 1 =
            r ^ 2 / Real.exp 1 * ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 := by ring
        push_cast at h1
        linarith
    have hint2 : Integrable (fun θ => ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2) (torusProb ι) :=
      integrable_of_bdd ((continuous_eval_torus f).norm.pow 2) ((∑ s ∈ f.support, ‖f.coeff s‖) ^ 2)
        (fun θ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_eval_torus_le f θ) 2)
    have hle : torusMean (MvPolynomial.C (r : ℂ) * f) ≤ r ^ 2 / Real.exp 1 * A / 2 := by
      unfold torusMean
      calc _ ≤ ∫ θ, r ^ 2 / Real.exp 1 * ‖MvPolynomial.eval (torusPoint θ) f‖ ^ 2 / 2 ∂(torusProb ι) :=
            integral_mono (hInt _ (mul_ne_zero hCc hf)) ((hint2.const_mul _).div_const 2) hpt
        _ = r ^ 2 / Real.exp 1 * A / 2 := by
            rw [integral_div, integral_const_mul, torus_parseval]
    have h12 : r ^ 2 / Real.exp 1 * A / 2 = 1 / 2 := by
      rw [hr2]; field_simp
    have hlogr : Real.log r = (1 - Real.log A) / 2 := by
      rw [hrdef, Real.log_sqrt hq.le, Real.log_div (Real.exp_pos 1).ne' hApos.ne', Real.log_exp]
    unfold polyL2
    rw [← hA, Real.log_sqrt hApos.le]
    linarith
  · intro s
    obtain ⟨θ₀, hθ₀⟩ := exists_torus_max f
    refine ⟨θ₀, ?_⟩
    rw [← torus_coeff_integral f s]
    have hb : ∀ᵐ θ ∂(torusProb ι), ‖MvPolynomial.eval (torusPoint θ) f * conj (torusMono θ s)‖ ≤
        ‖MvPolynomial.eval (torusPoint θ₀) f‖ :=
      Filter.Eventually.of_forall (fun θ => by simpa [norm_torusMono_eq_one] using hθ₀ θ)
    simpa using norm_integral_le_of_norm_le_const hb
end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
