-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lf_toMatrix_cp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:48.840493+00:00
-- url     : https://prove2.me/submissions/fa7aa030-4f48-4f69-bca5-1c2781ad3854

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (i a : Fin n) :
    LinearMap.toMatrix (fockBasis n) (fockBasis n) (cpFock i a) = lfP i a := rfl
end ReciprocityTheory.ChartRestriction.DS
