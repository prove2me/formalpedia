-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gaussAbs_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:34:34.693511+00:00
-- url     : https://prove2.me/submissions/da440c60-4a88-461c-a92d-d9e3de70c902

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Qdist
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Mathlib.NumberTheory.Height.NumberField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
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
theorem _root_.solution {κ : Type} [Fintype κ] (w : FinitePlace K) (c : K) (F : MvPolynomial κ K) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.C c * F) = w c * ReciprocityTheory.MultiplicativeHeights.gaussAbs w F := by
  by_cases hc : c = 0
  · subst hc
    simp [ReciprocityTheory.MultiplicativeHeights.gaussAbs]
  · have hw : 0 < w c := by
      first
        | exact w.pos_iff.mpr hc
        | exact (FinitePlace.pos_iff).mpr hc
    have hsupp : (MvPolynomial.C c * F).support = F.support := by
      rw [MvPolynomial.C_mul', MvPolynomial.support_smul_eq hc]
    unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
    rw [hsupp]
    simp_rw [MvPolynomial.coeff_C_mul, map_mul, Real.toNNReal_mul hw.le]
    rw [← NNReal.mul_finset_sup, NNReal.coe_mul, Real.coe_toNNReal _ hw.le]
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
