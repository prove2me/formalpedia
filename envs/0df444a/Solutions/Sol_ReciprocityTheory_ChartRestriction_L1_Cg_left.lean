-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Cg.left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:10:11.964016+00:00
-- url     : https://prove2.me/submissions/160e2ef7-ee76-4f2e-968b-18073cbc185f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_ksC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ks_one_sub_zetaC_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_add
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
namespace Cg
theorem _root_.solution {p : ℕ} {f g : PowerSeries ℂ} (h : Cg p f g) : CoeffIn (Rm p) f := by
  obtain ⟨hg, w, hw, rfl⟩ := h
  exact hg.add ((CoeffIn.ksC (ks_one_sub_zetaC_mem p)).mul hw)
end Cg
end ReciprocityTheory.ChartRestriction.L1
