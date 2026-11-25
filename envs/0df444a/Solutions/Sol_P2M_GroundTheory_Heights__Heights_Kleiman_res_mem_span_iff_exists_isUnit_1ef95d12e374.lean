-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_span_iff_exists_isUnit_1ef95d12e374
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:36:37.537538+00:00
-- url     : https://prove2.me/submissions/6e11c28f-b581-49ff-a249-13c9b1c8a3ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_span_chart_le_fc9294251641

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
theorem _root_.solution {R : Set Ω} {I J : Chart x} (hIJ : I.1 ⊆ J.1) (z : Ω) :
    z ∈ Submodule.span (chartRing S x J) R ↔ ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧
      (a : Ω) • z ∈ Submodule.span (chartRing S x I) R := by
  constructor
  · intro hz
    refine Submodule.span_induction (p := fun z _ => ∃ a : chartRing S x I, IsUnit (chartIncl hIJ a) ∧
      (a : Ω) • z ∈ Submodule.span (chartRing S x I) R) ?_ ?_ ?_ ?_ hz
    · intro w hw
      exact ⟨1, by rw [map_one]; exact isUnit_one,
        by rw [OneMemClass.coe_one, one_smul]; exact Submodule.subset_span hw⟩
    · exact ⟨1, by rw [map_one]; exact isUnit_one, by rw [smul_zero]; exact Submodule.zero_mem _⟩
    · rintro u v _ _ ⟨a₁, ha₁, hu⟩ ⟨a₂, ha₂, hv⟩
      refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
      have h1 := Submodule.smul_mem _ a₂ hu
      have h2 := Submodule.smul_mem _ a₁ hv
      rw [chartRing_smul_def, smul_eq_mul] at h1 h2
      convert Submodule.add_mem _ h1 h2 using 1
      simp only [smul_eq_mul, Subalgebra.coe_mul]; ring
    · rintro c u _ ⟨a, ha, hu⟩
      obtain ⟨a', ha', hc⟩ := exists_isUnit_mul_mem hIJ c
      refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
      have := Submodule.smul_mem _ (⟨_, hc⟩ : chartRing S x I) hu
      rw [chartRing_smul_def, smul_eq_mul] at this
      convert this using 1
      rw [chartRing_smul_def]; simp only [smul_eq_mul, Subalgebra.coe_mul]; ring
  · rintro ⟨a, ⟨u, hu⟩, haz⟩
    have hJ := res_span_chart_le hIJ haz
    have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hz : z = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • z) := by
      rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
    rw [hz]
    exact Submodule.smul_mem _ _ hJ
end GroundTheory.Heights₂.Heights.Kleiman
