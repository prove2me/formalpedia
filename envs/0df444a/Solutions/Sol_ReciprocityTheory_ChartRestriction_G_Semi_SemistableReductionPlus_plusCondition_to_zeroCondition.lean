-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.SemistableReductionPlus.plusCondition_to_zeroCondition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:28:10.294739+00:00
-- url     : https://prove2.me/submissions/0afbe2e4-2bf0-4651-a444-06d46dbecb2a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableReductionPlusSplit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_PlusConditionToZeroCondition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.Semi
namespace SemistableReductionPlus
theorem _root_.solution (h : SemistableReductionPlus) : SemistableReductionZero := by
  intro V _ _ _ _ K _ _ _ _ A _ hA
  obtain ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, h1, h2, h3, G, i10,
    h4, h5, h6, h7, h8, h9, -⟩ := h V K A hA
  exact ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, h1, h2, h3, G, i10,
    h4, h5, h6, h7, h8, h9⟩
end SemistableReductionPlus
end ReciprocityTheory.ChartRestriction.G.Semi
