-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.DetB.fac_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:54:42.279265+00:00
-- url     : https://prove2.me/submissions/367edc0f-ba30-45a6-96aa-7e0c7501c47b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianLiftIdentities
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_DetB_lipschitzConst_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_DetB_Dl_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_DetB_cl_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.DetB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.DetB
theorem _root_.solution (k r : ℕ) (l : Fin (r + 1)) (s : ℝ) (hs : 0 ≤ s) (h : Mat k r) (hM : 1 ≤ gN h) :
    ENNReal.ofReal (gN h ^ (-(((l.val : ℝ) + 1) * s))) ≤
      ENNReal.ofReal (cl k r l ^ s) * (‖Dl k r l h‖₊ : ℝ≥0∞) ^ (-s) := by
  have hM0 : 0 < gN h := by linarith
  have hc := cl_pos k r l
  have hK := lipschitzConst_nonneg k r
  have hD : ‖Dl k r l h‖ ≤ cl k r l * gN h ^ (l.val + 1) := by
    have := Dl_le k r l h
    rw [mul_pow, ← mul_assoc] at this
    refine this.trans ?_
    unfold cl
    have : 0 ≤ gN h ^ (l.val + 1) := by positivity
    nlinarith
  have hb : 0 < cl k r l * gN h ^ (l.val + 1) := mul_pos hc (pow_pos hM0 _)
  have h1 : (‖Dl k r l h‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (cl k r l * gN h ^ (l.val + 1)) := by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]; exact ENNReal.ofReal_le_ofReal hD
  have h2 : ENNReal.ofReal (cl k r l * gN h ^ (l.val + 1)) ^ (-s) ≤ (‖Dl k r l h‖₊ : ℝ≥0∞) ^ (-s) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow h1 hs)
  refine le_trans (le_of_eq ?_) (mul_le_mul' le_rfl h2)
  rw [ENNReal.ofReal_rpow_of_pos hb, ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]
  congr 1
  rw [Real.mul_rpow hc.le (pow_nonneg hM0.le _), Real.rpow_neg hc.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hM0.le, ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hc s).ne', one_mul]
  congr 1
  push_cast; ring
end ReciprocityTheory.ChartRestriction.DS.Xi.DetB
