-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_twist_mem_iff_e4733d843f95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:22:41.48858+00:00
-- url     : https://prove2.me/submissions/8fad8ed1-394d-499c-85a8-b6d9b9202a7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_exists_unit_mul_mem_of_span_3d253f35998c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_idealMod_loc_beabb2cef896

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
theorem _root_.solution (Q : LineBundle S x) (J' : Ideal (Poly S N)) (I J : Chart x)
    (h : I.1 ⊆ J.1) (y : Ω) :
    y ∈ (Q.twist (idealSys x J')).sub J ↔ ∃ a : chartRing S x I, IsUnit (chartIncl h a) ∧
      (a : Ω) • y ∈ (Q.twist (idealSys x J')).sub I := by
  constructor
  · intro hy
    refine exists_unit_mul_mem_of_span (G := {z | ∃ q ∈ (idealSys x J').sub J, ∃ y ∈ Q.sub J,
      z = q • y}) h ((Q.twist (idealSys x J')).sub I) ?_ hy
    rintro _ ⟨q, hq, z, hz, rfl⟩
    obtain ⟨a, ha, haq⟩ := idealMod_loc h J' hq
    obtain ⟨b, hb, hbz⟩ := (Q.mem_iff I J h z).mp hz
    refine ⟨a * b, by rw [map_mul]; exact ha.mul hb, ?_⟩
    have : ((a * b : chartRing S x I) : Ω) * (q • z) = ((a : Ω) * q) • ((b : Ω) • z) := by
      simp only [smul_eq_mul, MulMemClass.coe_mul]; ring
    rw [this]
    exact Submodule.subset_span ⟨_, haq, _, hbz, rfl⟩
  · rintro ⟨a, ⟨u, hu⟩, hay⟩
    have hJ := (Q.twist (idealSys x J')).mono I J h _ hay
    have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
      rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
    rw [hy]
    exact Submodule.smul_mem _ _ hJ
end GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
