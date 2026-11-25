-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.RLV_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:17.280856+00:00
-- url     : https://prove2.me/submissions/1400a60b-96cb-48a8-b497-a5f4c6298139

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric Kronecker
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {Q : Type} [Fintype Q] (g : Matrix (Fin n) (Fin n) ℂ) (x : REV n Q) :
    RLV g x = Matrix.of.symm (g * Matrix.of x) := rfl
end ReciprocityTheory.ChartRestriction.DS.S7
