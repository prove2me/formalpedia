-- Prove2me | solution 1 for P2M_CompanionTheory_WaveGrid_nq__le_f17512d0d1f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:54:34.39925+00:00
-- url     : https://prove2.me/submissions/d969988d-44ed-472d-b64a-de4cc8b35420

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqMovedExample
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid
open Formalism.FourierDecayAlt Finset GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
namespace CompanionTheory.WaveGrid
theorem _root_.solution (P : M.Par) (b CT : ℝ) (hb : 1 ≤ b) (hCT : 0 ≤ CT)
    (hTT : b ^ (-(CT * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T * P.T') :
    nqΛ P b ≤ b ^ ((5 + CT) * ((2 * P.r + 2 : ℕ) : ℝ)) := by
  set m : ℝ := ((2 * P.r + 2 : ℕ) : ℝ) with hm
  have hmr : m = 2 * (P.r : ℝ) + 2 := by rw [hm]; push_cast; ring
  have hb0 : (0 : ℝ) < b := by linarith
  have hr : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hm0 : 0 ≤ m := by rw [hmr]; positivity
  have h2 : b ^ (8 * P.r + 20) = b ^ (8 * (P.r : ℝ) + 20) := by
    rw [← Real.rpow_natCast]; push_cast; ring_nf
  have h3 : (P.T * P.T')⁻¹ ≤ b ^ (CT * m) := by
    rw [Real.rpow_neg hb0.le] at hTT
    have hpos : 0 < (b ^ (CT * m))⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos hb0 _)
    calc (P.T * P.T')⁻¹ ≤ ((b ^ (CT * m))⁻¹)⁻¹ := inv_anti₀ hpos hTT
      _ = b ^ (CT * m) := inv_inv _
  have hX : b ^ (8 * P.r + 20) / (P.T * P.T') ≤ (b ^ ((5 + CT) * m)) ^ 2 := by
    calc b ^ (8 * P.r + 20) / (P.T * P.T') ≤ b ^ (8 * (P.r : ℝ) + 20) * b ^ (CT * m) := by
          rw [div_eq_mul_inv, h2]
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = b ^ ((8 * (P.r : ℝ) + 20) + CT * m) := by rw [Real.rpow_add hb0 (8 * (P.r : ℝ) + 20)]
      _ ≤ b ^ ((5 + CT) * m + (5 + CT) * m) := by
          apply Real.rpow_le_rpow_of_exponent_le hb
          have hCTm : 0 ≤ CT * m := mul_nonneg hCT hm0
          have e : (5 + CT) * m + (5 + CT) * m = 10 * m + 2 * (CT * m) := by ring
          rw [e]
          linarith
      _ = (b ^ ((5 + CT) * m)) ^ 2 := by rw [Real.rpow_add hb0, sq]
  exact (Real.sqrt_le_left (Real.rpow_nonneg hb0.le _)).mpr hX
end CompanionTheory.WaveGrid
