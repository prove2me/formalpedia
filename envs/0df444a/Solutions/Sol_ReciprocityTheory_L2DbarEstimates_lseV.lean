-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.lseV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:02:53.555322+00:00
-- url     : https://prove2.me/submissions/98b415b5-d7fc-400c-8a5f-b317ed1bf181

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_logPshAt_exp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_logPshAt_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_log_sum_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution : LSEVStatement := by
  intro n m U u hU hu hpos x hx ξ
  have hxU : U ∈ 𝓝 x := hU.mem_nhds hx
  have hgood : ∀ i, ContDiffAt ℝ 2 (u i) x ∧ LogPshAt n (u i) x := by
    intro i
    rcases hu i with ⟨φ, hφ, hL, he⟩ | ⟨g, hg, he⟩
    · have hev : (fun y => Real.exp (φ y)) =ᶠ[𝓝 x] u i :=
        Filter.mem_of_superset hxU fun y hy => (he y hy).symm
      have hφx : ContDiffAt ℝ 2 φ x := hφ.contDiffAt hxU
      exact ⟨(Real.contDiff_exp.contDiffAt.comp x hφx).congr_of_eventuallyEq hev.symm,
        (logPshAt_exp hφx (hL x hx)).congr hev⟩
    · have hev : (fun y => Complex.normSq (g y)) =ᶠ[𝓝 x] u i :=
        Filter.mem_of_superset hxU fun y hy => (he y hy).symm
      have hgx : ContDiffAt ℂ 2 g x := hg.contDiffAt hxU
      have hgR : ContDiffAt ℝ 2 g x := hgx.restrict_scalars ℝ
      have hns : ContDiffAt ℝ 2 (fun y => Complex.normSq (g y)) x := by
        have h2 : ContDiffAt ℝ 2 (fun y => (g y * conj (g y)).re) x :=
          reCLM.contDiff.contDiffAt.comp x (hgR.mul (conjCLE.contDiff.contDiffAt.comp x hgR))
        refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
        simp [mul_conj]
      exact ⟨hns.congr_of_eventuallyEq hev.symm, (logPshAt_normSq hgx).congr hev⟩
  exact leviV_log_sum_nonneg (fun i => (hgood i).1) (fun i => (hgood i).2) (hpos x hx) ξ
end ReciprocityTheory.L2DbarEstimates
