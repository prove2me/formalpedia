-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_exists_unit_mul_mem_of_span_3d253f35998c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:35:05.284889+00:00
-- url     : https://prove2.me/submissions/7c7d6bb4-6c84-4b19-93c5-431a92755b8c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily

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
open GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
theorem _root_.solution {I J : Chart x} (h : I.1 ⊆ J.1)
    (M : Submodule (chartRing S x I) Ω) {G : Set Ω}
    (hG : ∀ g ∈ G, ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧ (a : Ω) * g ∈ M)
    {y : Ω} (hy : y ∈ Submodule.span (chartRing S x J) G) :
    ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧ (a : Ω) * y ∈ M := by
  induction hy using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => exact ⟨1, by simp, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
    have : ((a * b : chartRing S x I) : Ω) * (y + z) = b • ((a : Ω) * y) + a • ((b : Ω) * z) := by
      simp only [chartRing_smul_def, MulMemClass.coe_mul]; ring
    rw [this]
    exact M.add_mem (M.smul_mem b hay) (M.smul_mem a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbc⟩ := exists_isUnit_mul_mem h c
    refine ⟨b * a, by rw [map_mul]; exact hb.mul ha, ?_⟩
    have : ((b * a : chartRing S x I) : Ω) * (c • y) =
        (⟨_, hbc⟩ : chartRing S x I) • ((a : Ω) * y) := by
      simp only [chartRing_smul_def, MulMemClass.coe_mul]; ring
    rw [this]
    exact M.smul_mem _ hay
end GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
