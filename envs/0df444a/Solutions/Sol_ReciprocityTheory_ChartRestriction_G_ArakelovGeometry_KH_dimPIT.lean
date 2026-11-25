-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:07.528163+00:00
-- url     : https://prove2.me/submissions/85e6033c-cdc6-438a-aa9d-b4bbc960fbc7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDimSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDimA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_KH_KrullDimensionPrincipalIdeal_dimPIT__15db7215ea0f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
theorem _root_.solution : DimPITStatement := KrullDimensionPrincipalIdeal.dimPIT'
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
