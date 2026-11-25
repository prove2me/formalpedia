-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.evl_levi_expNeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:03:44.022805+00:00
-- url     : https://prove2.me/submissions/1d7dd748-c21a-4f37-906f-faa0a0b5b2c4

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_deriv_exp_neg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_deriv_neg_exp_neg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_contDiff_exp_neg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_contDiff_neg_exp_neg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_ckR
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_comp_real
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_comp_real
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_ofReal


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
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ)
    (hph : SmoothR n z ph) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => Real.exp (-ph y)) x ξ =
      ((Real.exp (-ph x) : ℝ) : ℂ) * (dDot n z (fun y => (ph y : ℂ)) x ξ *
        conj (dDot n z (fun y => (ph y : ℂ)) x ξ) - Levi n z ph x ξ) := by
  have hdb : ∀ k, db n z k (fun y => ((Real.exp (-ph y) : ℝ) : ℂ)) =
      fun y => ((-Real.exp (-ph y) : ℝ) : ℂ) * db n z k (fun y => (ph y : ℂ)) y := by
    intro k; funext y
    have := db_comp_real n z (fun t => Real.exp (-t)) contDiff_exp_neg ph (SmoothR.ckR n z 1 ph hph) k y
    rw [deriv_exp_neg] at this
    simpa using this
  have hf1 : Ck n z 1 (fun y => ((-Real.exp (-ph y) : ℝ) : ℂ)) :=
    SmoothR.ckR n z 1 _ (SmoothR.comp n z _ contDiff_neg_exp_neg ph hph)
  have hd2 : ∀ j, d n z j (fun y => ((-Real.exp (-ph y) : ℝ) : ℂ)) x =
      ((Real.exp (-ph x) : ℝ) : ℂ) * d n z j (fun y => (ph y : ℂ)) x := by
    intro j
    have := d_comp_real n z (fun t => -Real.exp (-t)) contDiff_neg_exp_neg ph (SmoothR.ckR n z 1 ph hph) j x
    rw [deriv_neg_exp_neg] at this
    simpa using this
  have h2 : ∀ j k, d n z j (db n z k (fun y => ((Real.exp (-ph y) : ℝ) : ℂ))) x =
      ((Real.exp (-ph x) : ℝ) : ℂ) * (d n z j (fun y => (ph y : ℂ)) x *
        conj (d n z k (fun y => (ph y : ℂ)) x) - d n z j (db n z k (fun y => (ph y : ℂ))) x) := by
    intro j k
    have hdbk : Ck n z 1 (db n z k (fun y => (ph y : ℂ))) :=
      Ck.db n z 1 k _ (SmoothR.ckR n z 2 ph hph)
    rw [hdb k, d_mul n z _ _ hf1 hdbk j x, hd2 j, db_ofReal n z ph k x]
    push_cast; ring
  have c : dDot n z (fun y => (ph y : ℂ)) x ξ * conj (dDot n z (fun y => (ph y : ℂ)) x ξ) =
      ∑ j, ∑ k, d n z j (fun y => (ph y : ℂ)) x * conj (d n z k (fun y => (ph y : ℂ)) x) *
        ξ j * conj (ξ k) := by
    unfold dDot
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul]; ring
  rw [c]
  unfold Levi
  simp only [h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring
end ReciprocityTheory.L2DbarEstimates.I
