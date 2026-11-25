-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Cg.symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:07:58.742121+00:00
-- url     : https://prove2.me/submissions/bf5f1e83-2cfe-49e5-97db-02052161dbc7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_ksC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_ksNeg
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
theorem _root_.solution {p : ℕ} {f g : PowerSeries ℂ} (h : Cg p f g) : Cg p g f := by
  obtain ⟨hg, w, hw, rfl⟩ := h
  exact ⟨hg.add ((CoeffIn.ksC (ks_one_sub_zetaC_mem p)).mul hw), -w, hw.ksNeg, by ring⟩
end Cg
end ReciprocityTheory.ChartRestriction.L1
