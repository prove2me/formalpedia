-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_res_exists_mul_mem_pow_f29f9a78302a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:10:46.603175+00:00
-- url     : https://prove2.me/submissions/89b3972e-4b9e-4a58-9ffb-74167517a400

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace LineBundle
theorem _root_.solution (H : LineBundle S x) {I J : Chart x} (hIJ : I.1 ⊆ J.1)
    (n : ℕ) {z : Ω} (hz : z ∈ (H.pow n).sub J) :
    ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧ (a : Ω) * z ∈ (H.pow n).sub I := by
  induction n generalizing z with
  | zero =>
    obtain ⟨a, ha, haz⟩ := ((twistBundle S x 0).mem_iff I J hIJ z).mp hz
    exact ⟨a, ha, haz⟩
  | succ n ih =>
    change z ∈ ((H.pow n).twist H.toSubSystem).sub J at hz
    change ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧
      (a : Ω) * z ∈ ((H.pow n).twist H.toSubSystem).sub I
    refine Submodule.span_induction (p := fun z _ => ∃ a : chartRing S x I,
      IsUnit (chartIncl hIJ a) ∧ (a : Ω) * z ∈ ((H.pow n).twist H.toSubSystem).sub I) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, w, hw, rfl⟩
      obtain ⟨a₁, ha₁, hq'⟩ := (H.mem_iff I J hIJ q).mp hq
      obtain ⟨a₂, ha₂, hw'⟩ := ih hw
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂,
        Submodule.subset_span ⟨_, hq', _, hw', ?_⟩⟩
      simp only [smul_eq_mul, Subalgebra.coe_mul]; ring
    · exact ⟨1, by rw [map_one]; exact isUnit_one, by rw [mul_zero]; exact Submodule.zero_mem _⟩
    · rintro u v _ _ ⟨a₁, ha₁, hu⟩ ⟨a₂, ha₂, hv⟩
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
      have h1 := Submodule.smul_mem _ a₂ hu
      have h2 := Submodule.smul_mem _ a₁ hv
      rw [chartRing_smul_def] at h1 h2
      convert Submodule.add_mem _ h1 h2 using 1
      simp only [Subalgebra.coe_mul]; ring
    · rintro c u _ ⟨a, ha, hu⟩
      obtain ⟨a', ha', hc⟩ := exists_isUnit_mul_mem hIJ c
      refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
      have := Submodule.smul_mem _ (⟨_, hc⟩ : chartRing S x I) hu
      rw [chartRing_smul_def] at this
      convert this using 1
      rw [chartRing_smul_def]; simp only [Subalgebra.coe_mul]; ring
end LineBundle
end GroundTheory.Heights₂.Heights.Kleiman
