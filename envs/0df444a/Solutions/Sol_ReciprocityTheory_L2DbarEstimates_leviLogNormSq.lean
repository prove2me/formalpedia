-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.leviLogNormSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:36:50.573524+00:00
-- url     : https://prove2.me/submissions/cfc4173a-ed4f-4a4c-b346-0e03274ec8cb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffAt_normSq_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_normSq_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_normSq_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviChain
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_ofReal_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_projPerp_sqNorm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_sqNorm_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_ofReal_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution : LeviLogNormSqStatement := by
  intro n p g x ξ hg hG
  set G : Fin p → ℂ := fun i => g i x with hGdef
  have hpos : 0 < sqNorm G := sqNorm_pos hG
  have hne : ((sqNorm G : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hv : ContDiffAt ℝ 2 (fun y => sqNorm (fun i => g i y)) x := by
    unfold sqNorm
    exact ContDiffAt.sum fun i _ => contDiffAt_normSq_comp (hg i)
  have hk : ContDiffAt ℝ 2 Real.log (sqNorm (fun i => g i x)) := Real.contDiffAt_log.mpr hpos.ne'
  have hc : leviV n (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) x ξ =
      ((deriv Real.log (sqNorm G) : ℝ) : ℂ) *
          leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ +
        ((deriv (deriv Real.log) (sqNorm G) : ℝ) : ℂ) *
          ((Complex.normSq (∑ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x * ξ j) :
            ℝ) : ℂ) :=
    leviChain n Real.log (fun y => sqNorm (fun i => g i y)) x ξ hv hk
  have hlv : leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ =
      ((sqNorm (wJac n p g x *ᵥ ξ) : ℝ) : ℂ) := by
    have h1 : leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ =
        ∑ i, leviV n (fun y => ((Complex.normSq (g i y) : ℝ) : ℂ)) x ξ :=
      leviV_ofReal_sum (u := fun i y => Complex.normSq (g i y))
        (fun i => contDiffAt_normSq_comp (hg i)) ξ
    rw [h1, sqNorm, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => leviV_normSq_comp (hg i) ξ
  have hwd : ∀ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x =
      ∑ i, wd n j (g i) x * conj (g i x) := by
    intro j
    have h1 : wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x =
        ∑ i, wd n j (fun y => ((Complex.normSq (g i y) : ℝ) : ℂ)) x :=
      wd_ofReal_sum (u := fun i y => Complex.normSq (g i y))
        (fun i => (contDiffAt_normSq_comp (hg i)).differentiableAt (by norm_num))
    rw [h1]
    exact Finset.sum_congr rfl fun i _ => wd_normSq_comp (hg i)
  have hS : ∑ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x * ξ j =
      star G ⬝ᵥ (wJac n p g x *ᵥ ξ) := by
    simp only [hwd, dotProduct, Matrix.mulVec, wJac, Pi.star_apply, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hGdef, Complex.star_def]
    ring
  rw [hc, hlv, hS, projPerp_sqNorm p G _ hG, Real.deriv_log, Real.deriv_log', deriv_inv]
  push_cast
  field_simp
  ring
end ReciprocityTheory.L2DbarEstimates
