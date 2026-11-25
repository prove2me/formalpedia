-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.jInv_eq_jT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:08:13.626297+00:00
-- url     : https://prove2.me/submissions/7b12fce6-c284-4433-b294-2b999fc683a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGEis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_disc_eq
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_g__eq_e5b5a7aa6c51
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_DD_ne_zero


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
theorem _root_.solution {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) : jInv L = jT τ := by
  have hc : c ≠ 0 := h.1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hDD : DD τ ≠ 0 := DD_ne_zero τ
  show 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = E₄ τ ^ 3 / DD τ
  rw [disc_eq h, g₂_eq h]
  field_simp
  ring
end ReciprocityTheory.ChartRestriction.L1
