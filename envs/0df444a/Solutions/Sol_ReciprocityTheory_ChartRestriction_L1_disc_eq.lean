-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.disc_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:59:06.070724+00:00
-- url     : https://prove2.me/submissions/1135d633-deb6-4200-bd8c-539e3aee8270

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGEis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_g__eq_e1cebfa140ec
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_g__eq_e5b5a7aa6c51


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
theorem _root_.solution {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (c ^ 12)⁻¹ * (4096 * (Real.pi : ℂ) ^ 12) * DD τ := by
  have hc : c ≠ 0 := h.1
  have hD : DD τ = (E₄ τ ^ 3 - E₆ τ ^ 2) / 1728 := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [g₂_eq h, g₃_eq h, hD]
  field_simp
  ring
end ReciprocityTheory.ChartRestriction.L1
