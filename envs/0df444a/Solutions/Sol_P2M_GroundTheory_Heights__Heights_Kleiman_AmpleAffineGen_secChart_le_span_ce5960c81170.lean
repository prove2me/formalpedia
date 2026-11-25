-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_secChart_le_span_ce5960c81170
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:09:50.730257+00:00
-- url     : https://prove2.me/submissions/d6908520-3f4f-4a6a-ba8a-36b840f3016c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_mem_ampleSubalg_of_mem_chartRing_9358b4af0d94
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
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
theorem _root_.solution (Q H : LineBundle S x) (m b : ℕ) {h : Ω} (h0 : h ≠ 0) (J : Chart x)
    (hh : h ∈ (H.pow m).sub J) {G : Set Ω}
    (hG : Submodule.span (chartRing S x J) G = (Q.twist (H.pow b)).sub J) {z : Ω}
    (hz : z ∈ secChart Q.toSubSystem H.toSubSystem m b h J) :
    z ∈ Submodule.span (ampleSubalg H.toSubSystem m h J hh) G := by
  obtain ⟨k, hk⟩ := hz
  have hF : ∀ y ∈ (Q.twist (H.pow b)).sub J,
      y ∈ Submodule.span (ampleSubalg H.toSubSystem m h J hh) G := by
    intro y hy
    rw [← hG] at hy
    induction hy using Submodule.span_induction with
    | mem g hg => exact Submodule.subset_span hg
    | zero => exact Submodule.zero_mem _
    | add _ _ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
    | smul a y _ h1 =>
      rw [chartRing_smul_def]
      exact Submodule.smul_mem _
        (⟨a, mem_ampleSubalg_of_mem_chartRing hh a.2⟩ : ampleSubalg H.toSubSystem m h J hh) h1
  have hdec : (Q.twist (H.pow (b + m * k))).sub J =
      (H.pow (m * k)).sub J * (Q.twist (H.pow b)).sub J := by
    simp only [SubSystem.twist_sub_eq_mul_of_line, SubSystem.pow_sub, pow_add]
    ring
  rw [hdec] at hk
  have key : ∀ y ∈ (H.pow (m * k)).sub J * (Q.twist (H.pow b)).sub J,
      y / h ^ k ∈ Submodule.span (ampleSubalg H.toSubSystem m h J hh) G := by
    intro y hy
    refine Submodule.mul_induction_on hy (fun w hw f hf => ?_) (fun y y' h1 h2 => ?_)
    · have hB : w / h ^ k ∈ ampleSubalg H.toSubSystem m h J hh :=
        ⟨k, by rwa [div_mul_cancel₀ _ (pow_ne_zero _ h0)]⟩
      have : w * f / h ^ k = (⟨_, hB⟩ : ampleSubalg H.toSubSystem m h J hh) • f := by
        rw [Subalgebra.smul_def, smul_eq_mul]
        ring
      rw [this]
      exact Submodule.smul_mem _ _ (hF f hf)
    · rw [add_div]
      exact Submodule.add_mem _ h1 h2
  have := key _ hk
  rwa [mul_div_cancel_right₀ _ (pow_ne_zero _ h0)] at this
end GroundTheory.Heights₂.Heights.Kleiman.AmpleAffineGen
