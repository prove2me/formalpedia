-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.normRV_u
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:35:25.06791+00:00
-- url     : https://prove2.me/submissions/e367b98c-8b81-41bb-abb2-197be7f7c663

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_norm_P0V_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_normRV_lt

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
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {ε : Fin n → Bool} {s : Bool} {u : Matrix (Fin n) (SgIxV ε s) ℂ} (hu : hsRV (u - signedIdentityColumns ε s) < 1 / 16) :
    ‖u‖ ≤ Real.sqrt n + 1 / 4 := by
  have h1 := normRV_lt hu
  have h2 := norm_P0V_le ε s
  calc ‖u‖ = ‖signedIdentityColumns ε s + (u - signedIdentityColumns ε s)‖ := by rw [add_sub_cancel]
    _ ≤ ‖signedIdentityColumns ε s‖ + ‖u - signedIdentityColumns ε s‖ := norm_add_le _ _
    _ ≤ Real.sqrt n + 1 / 4 := by linarith
end ReciprocityTheory.ChartRestriction.DS.S7
