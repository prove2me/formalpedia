-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.O_bddRV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:55.844805+00:00
-- url     : https://prove2.me/submissions/59f74b2a-c597-4af7-9914-a0d9f38953e0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hsRV_entry_le

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
theorem _root_.solution {ε : Fin n → Bool} {s : Bool} {x : REV n (SgIxV ε s)} (hx : hsRV (Matrix.of x - signedIdentityColumns ε s) < 1 / 16) :
    x ∈ closedBall (0 : REV n (SgIxV ε s)) 2 := by
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun j => ?_
  have h1 := hsRV_entry_le (Matrix.of x - signedIdentityColumns ε s) i j
  have h2 : ‖(Matrix.of x - signedIdentityColumns ε s) i j‖ < 1 / 4 := by
    nlinarith [norm_nonneg ((Matrix.of x - signedIdentityColumns ε s) i j)]
  have h3 : ‖signedIdentityColumns ε s i j‖ ≤ 1 := by
    simp only [signedIdentityColumns]
    split_ifs <;> simp
  have e : x i j = (Matrix.of x - signedIdentityColumns ε s) i j + signedIdentityColumns ε s i j := by simp
  rw [e]
  linarith [norm_add_le ((Matrix.of x - signedIdentityColumns ε s) i j) (signedIdentityColumns ε s i j)]
end ReciprocityTheory.ChartRestriction.DS.S7
