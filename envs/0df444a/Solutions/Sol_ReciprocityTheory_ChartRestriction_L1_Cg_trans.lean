-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Cg.trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:58:53.643897+00:00
-- url     : https://prove2.me/submissions/831fbd60-8b3b-465d-8dbf-ee3cdc8eae98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_add


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
theorem _root_.solution {p : ℕ} {f g h : PowerSeries ℂ} (h1 : Cg p f g) (h2 : Cg p g h) : Cg p f h := by
  obtain ⟨hg, w₁, hw₁, rfl⟩ := h1
  obtain ⟨hh, w₂, hw₂, rfl⟩ := h2
  exact ⟨hh, w₂ + w₁, hw₂.add hw₁, by ring⟩
end Cg
end ReciprocityTheory.ChartRestriction.L1
