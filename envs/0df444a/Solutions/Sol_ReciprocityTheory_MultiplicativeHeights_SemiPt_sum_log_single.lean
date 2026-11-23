-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.sum_log_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:25.786326+00:00
-- url     : https://prove2.me/submissions/8c04a1aa-6eba-4d40-a2a8-2c208cabd60b

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegT
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegR
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_sum_log_norm_emb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] (z : K) (hz : z ≠ 0) (d : ℝ)
    (hd : 0 < d) :
    ∑ σ : K →+* ℂ, Real.log (‖σ z‖ ^ 2 * d) =
      2 * Real.log |((Algebra.norm ℚ z : ℚ) : ℝ)| + (Fintype.card (K →+* ℂ) : ℝ) * Real.log d := by
  have h1 : ∀ σ : K →+* ℂ, Real.log (‖σ z‖ ^ 2 * d) = 2 * Real.log ‖σ z‖ + Real.log d := by
    intro σ
    have : ‖σ z‖ ≠ 0 := by simpa using hz
    rw [Real.log_mul (pow_ne_zero 2 this) hd.ne', Real.log_pow]
    push_cast
    ring
  simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, sum_log_norm_emb, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
end ReciprocityTheory.MultiplicativeHeights.SemiPt
