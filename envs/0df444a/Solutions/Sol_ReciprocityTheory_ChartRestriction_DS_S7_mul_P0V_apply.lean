-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.mul_P0V_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:44.367847+00:00
-- url     : https://prove2.me/submissions/3ed88814-6ff5-42f0-9a5a-d6ab25fc8357

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
theorem _root_.solution (ε : Fin n → Bool) (s : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (b : SgIxV ε s) :
    (g * signedIdentityColumns ε s) i b = g i b.1 := by
  simp [Matrix.mul_apply, signedIdentityColumns]
end ReciprocityTheory.ChartRestriction.DS.S7
