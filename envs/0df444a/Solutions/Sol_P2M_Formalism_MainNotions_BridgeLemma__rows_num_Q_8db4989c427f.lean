-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__rows_num_Q_8db4989c427f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:06.211773+00:00
-- url     : https://prove2.me/submissions/2033da2b-c528-42e0-9edc-36dddee5a02a

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsNum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsRpowPow
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__rows_rpow_pow_7d3f75c3e74b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open Formalism.HermitianLatticeCounting
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution {f r : ℕ} {b pe E1 cr δ : ℝ} (hb : 2 ≤ b) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) :
    (1 + δ) * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2) * ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2 ≤
      b ^ (1 + 12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + pe * (2 * E1 + 2 * cr + 6 * ((r : ℝ) + 1) ^ 2)) := by
  have hb0 : 0 < b := by linarith
  have hrp : ∀ y z : ℝ, (b ^ y) ^ z = b ^ (y * z) := fun y z => (Real.rpow_mul hb0.le y z).symm
  have h6 : (41 : ℝ) ≤ b ^ 6 := by
    have h2 : (2 : ℝ) ^ 6 ≤ b ^ 6 := by gcongr
    norm_num at h2
    linarith
  have h41 : (41 : ℝ) ^ f ≤ b ^ (6 * (f : ℝ)) := by
    calc (41 : ℝ) ^ f ≤ (b ^ 6) ^ f := by gcongr
      _ = b ^ (6 * (f : ℝ)) := by
        rw [← pow_mul, ← Real.rpow_natCast]
        congr 1 <;> push_cast <;> ring
  have e0 : (b ^ pe) ^ 3 = b ^ (3 * pe) := by
    rw [rows_rpow_pow hb0]
    congr 1 <;> push_cast <;> ring
  have hA : (41 : ℝ) ^ f * (b ^ pe) ^ 3 ≤ b ^ (6 * (f : ℝ) + 3 * pe) := by
    rw [Real.rpow_add hb0, e0]
    gcongr
    all_goals first | exact h41 | positivity
  have e1 : ((b ^ pe) ^ E1) ^ 2 = b ^ (2 * pe * E1) := by
    rw [hrp, rows_rpow_pow hb0]
    congr 1 <;> push_cast <;> ring
  have e2 : ((b ^ pe) ^ cr) ^ 2 = b ^ (2 * pe * cr) := by
    rw [hrp, rows_rpow_pow hb0]
    congr 1 <;> push_cast <;> ring
  have e3 : ((b ^ (6 * (f : ℝ) + 3 * pe)) ^ ((r + 1) ^ 2)) ^ 2 =
      b ^ (12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + 6 * pe * ((r : ℝ) + 1) ^ 2) := by
    rw [rows_rpow_pow hb0, rows_rpow_pow hb0]
    congr 1 <;> push_cast <;> ring
  have h1δ : 1 + δ ≤ b ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    linarith
  calc (1 + δ) * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2) * ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2
      ≤ b ^ (1 : ℝ) * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2) *
          ((b ^ (6 * (f : ℝ) + 3 * pe)) ^ ((r + 1) ^ 2)) ^ 2 := by
        gcongr
        all_goals first | exact h1δ | exact hA | positivity
    _ = b ^ (1 : ℝ) * (b ^ (2 * pe * E1) * b ^ (2 * pe * cr)) *
          b ^ (12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + 6 * pe * ((r : ℝ) + 1) ^ 2) := by
        rw [e1, e2, e3]
    _ = _ := by
        rw [← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_add hb0]
        congr 1
        ring
end Formalism.MainNotions.BridgeLemma₂
