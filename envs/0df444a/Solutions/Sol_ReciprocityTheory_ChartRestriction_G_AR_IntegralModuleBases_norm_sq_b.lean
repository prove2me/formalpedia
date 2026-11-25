-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.norm_sq_b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:29:39.501181+00:00
-- url     : https://prove2.me/submissions/fec13a8b-cffa-4878-bb6c-a2bb7546a31d

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_norm_sq_comb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
open Finset InnerProductSpace ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
theorem _root_.solution (b : Fin d → E) (hb : LinearIndependent ℝ b) (i : Fin d) :
    ‖b i‖ ^ 2 = ∑ j, mu b i j ^ 2 * ‖gs b j‖ ^ 2 := by
  have h := norm_sq_comb b hb (fun l => if l = i then (1:ℝ) else 0)
  have hs : ∑ l, (if l = i then (1:ℝ) else 0) • b l = b i := by simp
  have hn : ∀ j, nu b (fun l => if l = i then (1:ℝ) else 0) j = mu b i j := by
    intro j; simp [nu]
  rw [hs] at h; rw [h]; simp only [hn]
end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
