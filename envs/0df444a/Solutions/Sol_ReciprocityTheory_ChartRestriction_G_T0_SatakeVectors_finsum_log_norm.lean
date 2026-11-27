-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.finsum_log_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:40:29.418881+00:00
-- url     : https://prove2.me/submissions/1a1efba2-bf18-4229-b65f-cd005cb9f5b4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Qdist
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Mathlib.NumberTheory.Height.NumberField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_finsum_log_eq
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution (c : K) (hc : c ≠ 0) :
    ∑ᶠ w : FinitePlace K, Real.log (w c) = -Real.log |((Algebra.norm ℚ c : ℚ) : ℝ)| := by
  have hpos : ∀ w : FinitePlace K, 0 < w c := by
    intro w
    first
      | exact w.pos_iff.mpr hc
      | exact (FinitePlace.pos_iff).mpr hc
      | exact lt_of_le_of_ne (by positivity) (fun h => hc (by simpa using h.symm))
  rw [finsum_log_eq (fun w : FinitePlace K => w c) hpos (FinitePlace.mulSupport_finite hc),
    FinitePlace.prod_eq_inv_abs_norm hc]
  first
    | (rw [Rat.cast_inv, Rat.cast_abs, Real.log_inv])
    | (push_cast; rw [Real.log_inv])
    | simp [Real.log_inv]
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
