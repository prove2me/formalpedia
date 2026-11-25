-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.norm_fB_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:29:34.358287+00:00
-- url     : https://prove2.me/submissions/09a16024-e529-4bf3-a0cc-3a4822c075ef

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_IntegralModuleBasisStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsRedOf
import Definitions.Def_ReciprocityTheory_ReducedBases_PrefixProdGeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_DetToMatrixSq
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_Q_eq


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
open Finset InnerProductSpace Matrix ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open scoped MatrixOrder ComplexOrder
variable {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
theorem _root_.solution (A B : Matrix (Fin d) (Fin d) ℝ) (hAB : A = Bᴴ * B) (x : Fin d → ℤ) :
    ‖fB B x‖ ^ 2 = (fun i => (x i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (x i : ℝ)) := by
  have h := Q_eq A B hAB x
  simp only [Q, polar] at h
  have h2 : ‖fB B x‖ ^ 2 = toReal x ⬝ᵥ (A *ᵥ toReal x) := by linarith
  exact h2
end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
