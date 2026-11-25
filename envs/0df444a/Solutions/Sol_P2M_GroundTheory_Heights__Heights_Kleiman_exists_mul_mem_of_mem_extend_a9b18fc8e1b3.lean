-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_mem_of_mem_extend_a9b18fc8e1b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:39:57.118215+00:00
-- url     : https://prove2.me/submissions/9ffc2524-0744-4a1b-be60-1855e5d9ea73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_mem_chartRing_29135794d49d

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
  {x : Fin (N + 1) → Ω} {F : Type u} [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω]
  [IsFractionRing S F]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (Q : SubSystem S x Ω) (I : Chart x) {z : Ω}
    (hz : z ∈ (Q.extend F).sub I) : ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * z ∈ Q.sub I := by
  have hS : ∀ (t : S) {y : Ω}, y ∈ Q.sub I → algebraMap S Ω t * y ∈ Q.sub I := fun t y hy => by
    rw [← Algebra.smul_def]; exact (Q.sub I).smul_of_tower_mem t hy
  refine Submodule.span_induction
    (p := fun z _ => ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * z ∈ Q.sub I) ?_ ?_ ?_ ?_ hz
  · intro z hz
    exact ⟨1, one_mem _, by rw [map_one, one_mul]; exact hz⟩
  · exact ⟨1, one_mem _, by rw [mul_zero]; exact zero_mem _⟩
  · rintro a b _ _ ⟨t, ht, hta⟩ ⟨t', ht', htb⟩
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    have : algebraMap S Ω (t * t') * (a + b) =
        algebraMap S Ω t' * (algebraMap S Ω t * a) + algebraMap S Ω t * (algebraMap S Ω t' * b) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (hS t' hta) (hS t htb)
  · rintro a z _ ⟨t, ht, htz⟩
    obtain ⟨u, hu, hua⟩ := exists_mul_mem_chartRing (S := S) a.2
    refine ⟨u * t, mul_mem hu ht, ?_⟩
    have : algebraMap S Ω (u * t) * (a • z) =
        (⟨_, hua⟩ : chartRing S x I) • (algebraMap S Ω t * z) := by
      rw [chartRing_smul_def, chartRing_smul_def, map_mul]; ring
    rw [this]
    exact Submodule.smul_mem _ _ htz
end GroundTheory.Heights₂.Heights.Kleiman
