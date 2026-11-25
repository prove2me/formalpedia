-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__minkowski_discriminant_ineq_412dc0b620e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:28.969863+00:00
-- url     : https://prove2.me/submissions/4f28f59a-1edc-4ef5-89b3-5b2c46c29246

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_TraceInnerPosOfOrthonormalPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Module Formalism.HermitianLatticesTheory
open MeasureTheory
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) (Δ rd : ℝ) (hΔ : 0 < Δ) (hrd : rd ^ n = Δ) (hrd0 : 0 < rd) :
    Δ * 2 ^ (2 * n) < Real.sqrt (2 * n * rd) ^ (2 * n) * (√Real.pi ^ (2 * n) / Real.Gamma (((2 * n : ℕ) : ℝ) / 2 + 1)) := by
  have hpi : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have e1 : Real.sqrt (2 * n * rd) ^ (2 * n) = (2 * n * rd) ^ n := by
    rw [pow_mul, Real.sq_sqrt (by positivity)]
  have e2 : √Real.pi ^ (2 * n) = Real.pi ^ n := by
    rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
  have e3 : Real.Gamma (((2 * n : ℕ) : ℝ) / 2 + 1) = (n.factorial : ℝ) := by
    rw [show (((2 * n : ℕ) : ℝ) / 2 + 1) = (n : ℝ) + 1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
  rw [e1, e2, e3, mul_pow, mul_pow, hrd]
  have hf : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h2pi : (2 : ℝ) ^ n < Real.pi ^ n := pow_lt_pow_left₀ hpi (by norm_num) (by omega)
  have k1 : (2 : ℝ) ^ n * n.factorial < Real.pi ^ n * (n : ℝ) ^ n :=
    calc (2 : ℝ) ^ n * n.factorial ≤ 2 ^ n * (n : ℝ) ^ n := by gcongr
      _ < Real.pi ^ n * (n : ℝ) ^ n := by gcongr
  rw [← mul_div_assoc, lt_div_iff₀ hfpos]
  have q1 : Δ * 2 ^ (2 * n) * n.factorial = (Δ * 2 ^ n) * (2 ^ n * n.factorial) := by
    rw [two_mul, pow_add]; ring
  have q2 : 2 ^ n * (n : ℝ) ^ n * Δ * Real.pi ^ n = (Δ * 2 ^ n) * (Real.pi ^ n * (n : ℝ) ^ n) := by ring
  rw [q1, q2]
  exact mul_lt_mul_of_pos_left k1 (by positivity)
end Formalism.MainNotions.BridgeLemma₂
