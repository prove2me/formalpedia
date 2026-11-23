-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.isMF_DD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:23.860475+00:00
-- url     : https://prove2.me/submissions/14a7672f-968f-4b26-b62d-5f1823470802

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic

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
theorem _root_.solution : IsMF 12 DD := by
  first
    | exact ⟨ModularFormClass.modularForm ModularForm.discriminantCuspForm, fun τ => rfl⟩
    | exact ⟨ModularFormClass.modularForm CuspForm.discriminant, fun τ => rfl⟩
end ReciprocityTheory.ChartRestriction.L1
