-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.commutator_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:18.759545+00:00
-- url     : https://prove2.me/submissions/a46af265-f999-488e-b0dc-94ee889fe7a5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_Lemmata_MiscLemmasP_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Gelfand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (X Y Z : Module.End ℂ M) :
    X * (Y * Z) - Y * Z * X = (X * Y - Y * X) * Z + Y * (X * Z - Z * X) := by
  noncomm_ring
end ReciprocityTheory.ChartRestriction.DS
