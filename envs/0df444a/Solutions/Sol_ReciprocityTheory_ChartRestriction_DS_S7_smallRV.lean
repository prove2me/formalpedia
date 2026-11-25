-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.smallRV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:42:36.904349+00:00
-- url     : https://prove2.me/submissions/db380e0e-854b-427f-a79a-983f76b137c4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hs_le_colsV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hs_eq_frobVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hsRV_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_normRV_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_normRV_u

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
theorem _root_.solution {ε : Fin n → Bool} {s : Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    {u v : Matrix (Fin n) (SgIxV ε s) ℂ} (hu : hsRV (u - signedIdentityColumns ε s) < 1 / 16) (hv : hsRV (v - signedIdentityColumns ε s) < 1 / 16)
    (h : k * u = v) : hs k ≤ n + 2 * (5 / 2 * Real.sqrt n + 1 / 2) ^ 2 := by
  have hk' := hs_le_colsV s hk
  have hw := normRV_lt hu
  have hvn := normRV_u hv
  have hr0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hr2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have e1 : k * signedIdentityColumns ε s = v - k * (u - signedIdentityColumns ε s) := by
    rw [Matrix.mul_sub, h]
    abel
  have ha : ‖k * signedIdentityColumns ε s‖ ≤ ‖v‖ + ‖k‖ * ‖u - signedIdentityColumns ε s‖ := by
    have m1 : ‖k * (u - signedIdentityColumns ε s)‖ ≤ ‖k‖ * ‖u - signedIdentityColumns ε s‖ := Matrix.frobenius_norm_mul k (u - signedIdentityColumns ε s)
    have m2 := norm_sub_le v (k * (u - signedIdentityColumns ε s))
    rw [e1]
    linarith
  have hK : ‖k‖ ^ 2 ≤ n + 2 * ‖k * signedIdentityColumns ε s‖ ^ 2 := by
    have h0 := hk'
    rw [hs_eq_frobVG k, hsRV_eq (k * signedIdentityColumns ε s)] at h0
    exact h0
  have hKn := norm_nonneg k
  have han := norm_nonneg (k * signedIdentityColumns ε s)
  have hKw : ‖k‖ * ‖u - signedIdentityColumns ε s‖ ≤ ‖k‖ * (1 / 4) := mul_le_mul_of_nonneg_left hw.le hKn
  have hb : ‖k * signedIdentityColumns ε s‖ ≤ 5 / 2 * Real.sqrt n + 1 / 2 := by
    by_contra hc
    push_neg at hc
    have h1 : ‖k * signedIdentityColumns ε s‖ ≤ Real.sqrt n + 1 / 4 + ‖k‖ / 4 := by linarith
    have h4 : 0 ≤ 4 * (‖k * signedIdentityColumns ε s‖ - (Real.sqrt n + 1 / 4)) := by linarith
    have h5 : 4 * (‖k * signedIdentityColumns ε s‖ - (Real.sqrt n + 1 / 4)) ≤ ‖k‖ := by linarith
    have h16 := mul_le_mul h5 h5 h4 hKn
    have hd : 0 ≤ ‖k * signedIdentityColumns ε s‖ - (5 / 2 * Real.sqrt n + 1 / 2) := by linarith
    nlinarith [sq_nonneg (‖k * signedIdentityColumns ε s‖ - (5 / 2 * Real.sqrt n + 1 / 2)), mul_nonneg hd hr0, sq_nonneg (Real.sqrt n)]
  rw [hsRV_eq (k * signedIdentityColumns ε s)] at hk'
  have hb2 : ‖k * signedIdentityColumns ε s‖ ^ 2 ≤ (5 / 2 * Real.sqrt n + 1 / 2) ^ 2 := pow_le_pow_left₀ han hb 2
  linarith
end ReciprocityTheory.ChartRestriction.DS.S7
