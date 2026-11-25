-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_I2_IsU_zsmul__b8e6a11e43d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:33.897256+00:00
-- url     : https://prove2.me/submissions/db5e75f4-91e9-4668-aaa8-72849d7f94a3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceMinima
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitU
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}
namespace ReciprocityTheory.ChartRestriction.G.I2
namespace IsU
theorem _root_.solution {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim} (k : ℤ) (hu : IsU I x u) :
    IsU I (k • x) (k • u) := by
  refine ⟨zsmul_mem hu.1 k, fun a ha => ?_⟩
  have hH : Hf (k • x) a = (k : ℂ) * Hf x a := by
    simp only [Hf]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_assoc]
  rw [← Int.cast_smul_eq_zsmul ℝ k u, real_inner_smul_left, hu.2 a ha, hH]
  simp
end IsU
end ReciprocityTheory.ChartRestriction.G.I2
