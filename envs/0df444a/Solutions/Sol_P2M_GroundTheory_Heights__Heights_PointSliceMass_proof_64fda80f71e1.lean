-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointSliceMass_proof_64fda80f71e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:07:44.667983+00:00
-- url     : https://prove2.me/submissions/f9e9041a-c886-4f2e-b8b5-b766ea0510b6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPointSliceMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointChowForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPointIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPointSliceMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointSliceMass_isMultiHomog_pairing_11b476f2c29b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointSliceMass_line_sup_eq_ker_6fb74c079fa9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointChowForm_proof_efe26cd777c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointIntegral_proof_11cfe16df696
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_proof_60a02c7c6efe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open PointSliceMass
namespace GroundTheory.Heights₂.Heights
namespace PointSliceMass
theorem _root_.solution : PointSliceMass.Statement := by
  intro n δ h J f ℓ hJ hf hδ hℓ
  obtain ⟨y, hy0, hV, hline⟩ := PointLine.proof n J f hJ hf
  obtain ⟨c, hc0, hfc⟩ := PointChowForm.proof n J f y hf hy0 hV
  have hδ1 : δ = 1 := by
    have h1 : IsMultiHomog 1 f := by
      rw [hfc]
      unfold IsMultiHomog
      simpa using (isWeightedHomogeneous_C (groupWeight 1 n) c).mul (isMultiHomog_pairing y)
    exact congrFun (IsWeightedHomogeneous.inj_right hf.1 hδ h1) 0
  have hly : ∑ a, ℓ a * y a ≠ 0 := by
    intro h0
    apply hℓ
    rw [hline]
    intro t
    simp only [linForm, map_sum, map_mul, eval_C, eval_X, Pi.smul_apply, smul_eq_mul]
    rw [← mul_zero t, ← h0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [line_sup_eq_ker y ℓ J hline hly, PointIntegral.proof, hδ1, Nat.cast_one]
end PointSliceMass
end GroundTheory.Heights₂.Heights
