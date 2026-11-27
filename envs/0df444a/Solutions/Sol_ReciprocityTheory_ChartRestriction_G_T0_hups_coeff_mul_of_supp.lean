-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hups_coeff_mul_of_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T06:07:49.283428+00:00
-- url     : https://prove2.me/submissions/36047005-9c85-42c8-84ad-76889323e19c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_MinkSat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SatDegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsChooseRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PolyL2EqSqrtCoeffSum
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {σ R : Type*} [CommRing R] (F P : MvPolynomial σ R)
    (S : Finset (σ →₀ ℕ)) (hP : P.support ⊆ S) (t : σ →₀ ℕ) :
    (F * P).coeff t = ∑ m : S, P.coeff m * (F * MvPolynomial.monomial (m : σ →₀ ℕ) 1).coeff t := by
  classical
  have hPs : P = ∑ m ∈ S, MvPolynomial.monomial m (P.coeff m) := by
    conv_lhs => rw [P.as_sum]
    exact Finset.sum_subset hP fun m _ hm => by simp [MvPolynomial.notMem_support_iff.1 hm]
  conv_lhs => rw [hPs]
  rw [Finset.mul_sum, MvPolynomial.coeff_sum, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show MvPolynomial.monomial (m : σ →₀ ℕ) (P.coeff m) =
      MvPolynomial.C (P.coeff m) * MvPolynomial.monomial (m : σ →₀ ℕ) 1 by
    rw [MvPolynomial.C_mul_monomial, mul_one]]
  rw [mul_left_comm, MvPolynomial.coeff_C_mul]
end ReciprocityTheory.ChartRestriction.G.T0
