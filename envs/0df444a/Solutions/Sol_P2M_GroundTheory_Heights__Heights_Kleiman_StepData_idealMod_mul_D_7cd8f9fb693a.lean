-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepData_idealMod_mul_D_7cd8f9fb693a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:58:52.936534+00:00
-- url     : https://prove2.me/submissions/cfe1e699-d419-4b5e-9f96-0ff720c40a91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimSeq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_div_mem_chartRing_2fc244ce67c4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepData_form_mem_J_2ff6bfe963bf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepData_isUnit_D_53d41fd9d7c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_mem_form_fa180a587675


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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
variable (T : StepData k x)
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace StepData
theorem _root_.solution (hZ : ZeroIdealChart.Statement.{u, w}) (I : Chart x) :
    idealMod T.J I * T.D.sub I = Submodule.span (chartRing k x I) {T.si} := by
  apply le_antisymm
  · refine Submodule.mul_le.mpr fun a ha δ hδ => ?_
    obtain ⟨g, s, e, hg, hs, hge, hse, rfl⟩ := idealMod_mem_form T.J I ha
    obtain ⟨o, ho, hgo⟩ := T.form_mem_J hg hge I hδ
    refine Submodule.mem_span_singleton.mpr ⟨⟨o / aeval x s, div_mem_chartRing I ho hs hse⟩, ?_⟩
    rw [chartRing_smul_def]
    change o / aeval x s * T.si = aeval x g / aeval x s * δ
    rw [div_mul_eq_mul_div (aeval x g), hgo]
    ring
  · obtain ⟨Q', hQ'⟩ := (T.isUnit_D I).exists_right_inv
    have hle : Submodule.span (chartRing k x I) {T.si} * Q' ≤ idealMod T.J I := by
      refine Submodule.mul_le.mpr fun a ha b hb => ?_
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ c (hZ k Ω N x T I b fun δ hδ => ?_)
      have h1 : b * δ ∈ T.D.sub I * Q' := by
        rw [mul_comm b]; exact Submodule.mul_mem_mul hδ hb
      rw [hQ', Submodule.mem_one] at h1
      obtain ⟨y, hy⟩ := h1
      rw [← hy]; exact y.2
    calc Submodule.span (chartRing k x I) {T.si}
        = Submodule.span (chartRing k x I) {T.si} * Q' * T.D.sub I := by
          rw [mul_assoc, mul_comm Q', hQ', mul_one]
      _ ≤ idealMod T.J I * T.D.sub I := Submodule.mul_le.mpr fun a ha b hb => Submodule.mul_mem_mul (hle ha) hb
end StepData
end GroundTheory.Heights₂.Heights.Kleiman
