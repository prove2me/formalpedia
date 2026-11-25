-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.evl_dDot_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:27:08.503514+00:00
-- url     : https://prove2.me/submissions/649587b5-c18b-4e7d-afe2-8ce846b2078a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_dDot_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_db_eq_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_ck
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open scoped ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : M → ℂ)
    (hg : Holo n z g) (x : M) (ξ : Fin n → ℂ) :
    dDot n z (fun y => ((‖g y‖ ^ 2 : ℝ) : ℂ)) x ξ = conj (g x) * dDot n z g x ξ := by
  have hs : Smooth n z g := Holo.smooth n z g hg
  have h1 : Ck n z 1 g := Smooth.ck n z 1 g hs
  have hsq : (fun y => ((‖g y‖ ^ 2 : ℝ) : ℂ)) = fun y => g y * conj (g y) := by
    funext y; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hsq, evl_dDot_mul n z _ _ h1 (Ck.conj n z 1 g h1)]
  have h0 : dDot n z (fun y => conj (g y)) x ξ = 0 := by
    unfold dDot
    simp only [d_conj, Holo.db_eq_zero n z g hg, map_zero, zero_mul, Finset.sum_const_zero]
  rw [h0]; ring
end ReciprocityTheory.L2DbarEstimates.I
