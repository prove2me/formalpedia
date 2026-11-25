-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_smul_mem_twist_of_inv_1108d97397dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:38.035064+00:00
-- url     : https://prove2.me/submissions/2a38fb27-43db-4337-a4e9-c0ab0690b1a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZColumnsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZColumnsCechPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZColumns
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZColumns_chart_smul_e2cb3280eb9c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_25f1e2a30df9


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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  {r : ℕ}
omit [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
theorem _root_.solution {G : SubSystem S x E} {H : SubSystem S x Ω} {I : Chart x} {m c : ℕ}
    {w : Ω} (hw : ∀ q ∈ H.sub I ^ m, w * q ∈ chartRing S x I) {z : E}
    (hz : z ∈ (G.twist (H.pow (c + m))).sub I) : w • z ∈ (G.twist (H.pow c)).sub I := by
  change z ∈ Submodule.span _ _ at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, hq, y, hy, rfl⟩ := hy
    rw [SubSystem.pow_sub, pow_add] at hq
    refine Submodule.subset_span ⟨w * q, ?_, y, hy, by rw [smul_smul]⟩
    rw [SubSystem.pow_sub]
    refine Submodule.mul_induction_on hq (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · have e1 : w * (a * b) = (⟨w * b, hw b hb⟩ : chartRing S x I) • a := by
        rw [chartRing_smul_def]; ring
      rw [e1]
      exact Submodule.smul_mem _ _ ha
    · rw [mul_add]; exact add_mem ha hb
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ hy hy' => rw [smul_add]; exact add_mem hy hy'
  | smul a y _ hy =>
    have e1 : w • (a • y) = a • (w • y) := by
      rw [chart_smul, chart_smul, smul_smul, smul_smul, mul_comm]
    rw [e1]
    exact Submodule.smul_mem _ a hy
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZColumns
