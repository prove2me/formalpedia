-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.hsRV_P0V_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:19.763911+00:00
-- url     : https://prove2.me/submissions/d5328181-4736-424f-b49e-5463179127cb

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
theorem _root_.solution (ε : Fin n → Bool) (s : Bool) : hsRV (signedIdentityColumns ε s) ≤ n := by
  have h1 : hsRV (signedIdentityColumns ε s) = Fintype.card (SgIxV ε s) := by
    unfold hsRV signedIdentityColumns
    rw [Finset.sum_comm]
    simp [apply_ite]
  rw [h1]
  have h2 := Fintype.card_subtype_le (fun a : Fin n => ε a = s)
  have h3 : ((Fintype.card (SgIxV ε s) : ℕ) : ℝ) ≤ ((Fintype.card (Fin n) : ℕ) : ℝ) := by
    exact_mod_cast h2
  simpa using h3
end ReciprocityTheory.ChartRestriction.DS.S7
