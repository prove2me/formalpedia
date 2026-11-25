-- Prove2me | solution 1 for P2M_Formalism_L2_Pj_Crude_cro_ordGe_zero__ecad83ed03f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:45:26.022317+00:00
-- url     : https://prove2.me/submissions/091355b8-1d1e-4e15-8735-fd4a933772ee

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (t : ℕ) : OrdGe t (0 : PS k n d) := by
  intro m _
  exact map_zero _
end Formalism.L2.Pj.Crude
