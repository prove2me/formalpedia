-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kronSq_isMF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:13.452373+00:00
-- url     : https://prove2.me/submissions/85d4ee10-3ddf-4bc1-b4f8-e954b30ce609

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalMF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQExpEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGmQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_IsIntegralOfRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronPt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Cg_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Cg_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_congr_weight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_LowUnit_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_isMF_AA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_isMF_DD


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
theorem _root_.solution (p : ℕ) :
    IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (fun τ => (AA τ * DD τ ^ p - AA τ ^ p * DD τ) ^ 2) := by
  have h1 : IsMF (12 + ((p : ℕ) : ℤ) * 12) (fun τ => AA τ * DD τ ^ p) := isMF_AA.mul (isMF_DD.pow p)
  have h2 : IsMF (12 + ((p : ℕ) : ℤ) * 12) (fun τ => AA τ ^ p * DD τ) :=
    ((isMF_AA.pow p).mul isMF_DD).congr_weight (by ring)
  have h3 := (h1.sub h2).pow 2
  exact h3.congr_weight (by push_cast; ring)
end ReciprocityTheory.ChartRestriction.L1
