-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.fsLp_smul_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:40.032187+00:00
-- url     : https://prove2.me/submissions/749835bb-3ca8-4161-899b-0ed8058ae5bc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_FsMetricFinIsSemipositive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (w : ι → ℂ) : fsLp ι (Complex.I • w) = Complex.I • fsLp ι w := rfl
end ReciprocityTheory.ChartRestriction.G.Geo
