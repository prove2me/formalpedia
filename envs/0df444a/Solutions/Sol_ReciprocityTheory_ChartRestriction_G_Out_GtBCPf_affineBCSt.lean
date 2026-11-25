-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.affineBCSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:04.627713+00:00
-- url     : https://prove2.me/submissions/01b1792d-3b49-425e-8bdc-43f30c0f8955

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_AffineBCSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_Affine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_AffineSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_coord_affineBC


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution : AffineBCSt := by
  intro G B G' B' g q' q b sq hq X _ V hV V' hV' hle hleG φ φ' hφ' hφ
  exact coord_affineBC sq hq hV hV' hle hleG φ φ' hφ' hφ
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
