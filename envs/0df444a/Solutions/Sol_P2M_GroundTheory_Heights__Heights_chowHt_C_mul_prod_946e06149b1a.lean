-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chowHt_C_mul_prod_946e06149b1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:15.395662+00:00
-- url     : https://prove2.me/submissions/a2c292d0-8879-41f8-8905-e041c6ed3767

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowHt_pow_660460443bac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowHeightConst_8b6933d50429


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
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (hMul : ChowHeightMul.Statement) (H : ArchData K n) {k : ℕ} {ι : Type*}
    (s : Finset ι) (m d : ι → ℕ) (g : ι → MvPolynomial (Fin k × Fin n) K) (hg : ∀ i ∈ s, g i ≠ 0)
    {c : K} (hc : c ≠ 0) :
    chowHt H k (∑ i ∈ s, m i * d i) (C c * ∏ i ∈ s, g i ^ m i) =
      ∑ i ∈ s, (m i : ℝ) * chowHt H k (d i) (g i) := by
  classical
  have hP : ∀ t ⊆ s, ∏ i ∈ t, g i ^ m i ≠ 0 := fun t ht =>
    Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hg i (ht hi))
  have hprod : ∀ t ⊆ s, chowHt H k (∑ i ∈ t, m i * d i) (∏ i ∈ t, g i ^ m i) =
      ∑ i ∈ t, (m i : ℝ) * chowHt H k (d i) (g i) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.sum_empty, Finset.prod_empty, Finset.sum_empty, ← C_1]
      exact chowHeightConst K n k H 1 one_ne_zero
    | insert a t ha ih =>
      intro hts
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
        hMul K n H k _ _ _ _ (pow_ne_zero _ (hg a (hts (Finset.mem_insert_self a t))))
          (hP t (fun x hx => hts (Finset.mem_insert_of_mem hx))),
        chowHt_pow hMul H _ (hg a (hts (Finset.mem_insert_self a t))),
        ih (fun x hx => hts (Finset.mem_insert_of_mem hx))]
  have := hMul K n H k 0 (∑ i ∈ s, m i * d i) (C c) _ (C_ne_zero.mpr hc) (hP s le_rfl)
  rw [zero_add] at this
  rw [this, chowHeightConst K n k H c hc, zero_add, hprod s le_rfl]
end GroundTheory.Heights₂.Heights
