-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.isOpen_Dset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:42:01.618936+00:00
-- url     : https://prove2.me/submissions/a903599c-6e12-4a4a-96bb-cfd4cf3036fd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LiftFactorization
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetMonoDetOneAdd
import Definitions.Def_Lemmata_PosDefOfRealQuadratic_QuadFormRealSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_cont_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_isOpen_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
theorem _root_.solution (f p q : ℕ) : IsOpen (Dset f p q) :=
  isOpen_of (fun v : V (nD f p q) => v) cont_coord
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
