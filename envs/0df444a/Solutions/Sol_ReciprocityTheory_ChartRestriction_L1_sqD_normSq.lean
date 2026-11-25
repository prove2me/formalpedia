-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.sqD_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:42.310708+00:00
-- url     : https://prove2.me/submissions/855938c6-f9dd-4710-b04e-1c1f21dfff38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerPoly
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HasCMByStable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerPrin
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (d r : ℕ) : Complex.normSq ((r : ℂ) + redSqD d) = ((r ^ 2 + d : ℕ) : ℝ) := by
  unfold redSqD omegaK
  have h : (r : ℂ) + (2 * ((1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2) - 1)
      = ⟨(r : ℝ), Real.sqrt d⟩ := by
    apply Complex.ext <;> simp <;> ring
  rw [h, Complex.normSq_mk, Real.mul_self_sqrt (Nat.cast_nonneg d)]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.L1
