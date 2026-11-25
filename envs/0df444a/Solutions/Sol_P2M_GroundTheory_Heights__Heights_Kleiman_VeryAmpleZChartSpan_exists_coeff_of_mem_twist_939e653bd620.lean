-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_exists_coeff_of_mem_twist_939e653bd620
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:30:50.331643+00:00
-- url     : https://prove2.me/submissions/9e193e36-206b-4039-9baf-513151501ebd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZChartSpan
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_chart_smul_52f18409990f

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
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZChartSpan
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZChartSpan
theorem _root_.solution (F : SubSystem S x E) (Q : SubSystem S x Ω) (I : Chart x) (g : Finset E)
    (hg : F.sub I ≤ Submodule.span (chartRing S x I) (g : Set E)) {z : E} (hz : z ∈ (F.twist Q).sub I) :
    ∃ γ : E → Ω, (∀ y ∈ g, γ y ∈ Q.sub I) ∧ z = ∑ y ∈ g, γ y • y := by
  change z ∈ Submodule.span _ _ at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨q, hq, y', hy', rfl⟩ := hz
    obtain ⟨a, -, ha⟩ := Submodule.mem_span_finset.mp (hg hy')
    refine ⟨fun y => (a y : Ω) * q, fun y _ => ?_, ?_⟩
    · have := Submodule.smul_mem (Q.sub I) (a y) hq
      rwa [chartRing_smul_def] at this
    · rw [← ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [chart_smul, smul_smul, mul_comm]
  | zero => exact ⟨0, fun _ _ => Submodule.zero_mem _, by simp⟩
  | add z z' _ _ ih ih' =>
    obtain ⟨γ, hγ, rfl⟩ := ih
    obtain ⟨γ', hγ', rfl⟩ := ih'
    refine ⟨γ + γ', fun y hy => Submodule.add_mem _ (hγ y hy) (hγ' y hy), ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [Pi.add_apply, add_smul]
  | smul a z _ ih =>
    obtain ⟨γ, hγ, rfl⟩ := ih
    refine ⟨fun y => (a : Ω) * γ y, fun y hy => ?_, ?_⟩
    · have := Submodule.smul_mem (Q.sub I) a (hγ y hy)
      rwa [chartRing_smul_def] at this
    · rw [chart_smul, Finset.smul_sum]
      exact Finset.sum_congr rfl fun y _ => by rw [smul_smul]
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZChartSpan
