-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Domination_div_mem_of_mem_pullPow_8800596b5cce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:22:00.997253+00:00
-- url     : https://prove2.me/submissions/aeddea23-8504-424c-8f76-e0acfeef698b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_chartRing_base_of_mem_04507d5011a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Domination_mem_chartRing_base_of_base_f1a1460fb985

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.Domination
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}
variable {i : Fin (N + 1)} (hi : x i ≠ 0) {j : Fin (N' + 1)} (hj : x' j ≠ 0)
namespace GroundTheory.Heights₂.Heights.Kleiman.Domination
theorem _root_.solution : ∀ (n : ℕ) {y : Ω}, y ∈ pullPow (S := S) x x' n (singleChart hj) →
    y / x i ^ n ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj)
  | 0, y, hy => by
    rw [pow_zero, div_one]
    exact mem_chartRing_base_of_mem hi hj y ((mem_pullPow_zero_iff _ y).mp hy)
  | n + 1, y, hy => by
    rw [pullPow_succ] at hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨q, hq, y', hy', rfl⟩ := hw
      change q ∈ Submodule.span _ (Set.range x) at hq
      have hq' : q / x i ∈ chartRing (chartRing S x (singleChart hi)) x' (singleChart hj) := by
        induction hq using Submodule.span_induction with
        | mem q hq =>
          obtain ⟨l, rfl⟩ := hq
          exact mem_chartRing_base_of_base hi hj _ (ratio (S := S) hi l).2
        | zero => rw [zero_div]; exact zero_mem _
        | add a b _ _ ha hb => rw [add_div]; exact add_mem ha hb
        | smul c a _ ha =>
          rw [chartRing_smul_def, mul_div_assoc]
          exact mul_mem (mem_chartRing_base_of_mem hi hj _ c.2) ha
      have h := mul_mem hq' (solution n hy')
      rw [smul_eq_mul, pow_succ]
      rwa [div_mul_div_comm, mul_comm (x i) (x i ^ n)] at h
    | zero => rw [zero_div]; exact zero_mem _
    | add a b _ _ ha hb => rw [add_div]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [chartRing_smul_def, mul_div_assoc]
      exact mul_mem (mem_chartRing_base_of_mem hi hj _ c.2) ha
end GroundTheory.Heights₂.Heights.Kleiman.Domination
