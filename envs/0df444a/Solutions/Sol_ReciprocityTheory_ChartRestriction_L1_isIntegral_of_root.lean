-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.isIntegral_of_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:57:52.576033+00:00
-- url     : https://prove2.me/submissions/686f96ec-6b11-44af-b14c-e2ffcd2d565e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLatTau
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModCMPoint
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_IsIntegralOfRoot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LowUnit_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {P : Polynomial ℂ} (hP : ∀ i, IsIntegral ℤ (P.coeff i))
    (hu : IsIntegral ℤ (P.leadingCoeff)⁻¹) (h0 : P.leadingCoeff ≠ 0) {x : ℂ} (hx : P.eval x = 0) :
    IsIntegral ℤ x := by
  have hmon : (Polynomial.C (P.leadingCoeff)⁻¹ * P).Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ h0)
  have hdeg : (Polynomial.C (P.leadingCoeff)⁻¹ * P).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_C_mul (inv_ne_zero h0)]
    intro hd
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd, Polynomial.eval_C] at hx
    apply h0
    rw [Polynomial.leadingCoeff, hd]
    exact hx
  refine IsIntegral.of_aeval_monic_of_isIntegral_coeff hmon hdeg ?_ ?_
  · rw [Polynomial.eval_mul, hx, mul_zero]
    exact isIntegral_zero
  · intro i
    rw [Polynomial.coeff_C_mul]
    exact hu.mul (hP i)
end ReciprocityTheory.ChartRestriction.L1
