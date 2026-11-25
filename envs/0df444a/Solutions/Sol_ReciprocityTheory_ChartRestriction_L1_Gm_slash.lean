-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Gm_slash
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:54:01.423912+00:00
-- url     : https://prove2.me/submissions/b38a57ce-c85e-4ec4-9865-0bc70baf124b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmSlash
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmForm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Gm_smul


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
theorem _root_.solution {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) :
    (Gm m) ∣[24 * ((Tm m).card : ℤ)] γ = Gm m := by
  funext τ
  rw [SL_slash_apply, Gm_smul hm γ τ]
  have hd : denom γ τ ≠ 0 := denom_ne_zero _ τ
  have : (24 * ((Tm m).card : ℤ)) = ((24 * (Tm m).card : ℕ) : ℤ) := by push_cast; ring
  rw [this, zpow_neg, zpow_natCast]
  field_simp
end ReciprocityTheory.ChartRestriction.L1
