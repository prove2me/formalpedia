-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_span_secs_eq_secs_extend_88515a1497d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:54:31.42393+00:00
-- url     : https://prove2.me/submissions/295788a7-cb89-4e55-b1b8-9c72e818f111

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_mem_of_mem_extend_a9b18fc8e1b3

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
theorem _root_.solution (Q : SubSystem S x Ω) :
    Submodule.span F (Q.secs : Set Ω) = (Q.extend F).secs := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.mpr fun z hz => ?_
    rw [SetLike.mem_coe, SubSystem.secs, Submodule.mem_iInf] at hz ⊢
    intro I
    exact Submodule.subset_span (hz I)
  · intro z hz
    rw [SubSystem.secs, Submodule.mem_iInf] at hz
    choose t ht htz using fun I => exists_mul_mem_of_mem_extend Q I (hz I)
    have hS : ∀ (I : Chart x) (t : S) {y : Ω}, y ∈ Q.sub I → algebraMap S Ω t * y ∈ Q.sub I :=
      fun I t y hy => by rw [← Algebra.smul_def]; exact (Q.sub I).smul_of_tower_mem t hy
    set t₀ := ∏ I, t I with ht₀
    have ht₀m : t₀ ∈ nonZeroDivisors S := prod_mem fun I _ => ht I
    have hmem : algebraMap S Ω t₀ * z ∈ Q.secs := by
      rw [SubSystem.secs, Submodule.mem_iInf]
      intro I
      rw [ht₀, ← Finset.mul_prod_erase _ _ (Finset.mem_univ I), map_mul, mul_comm (algebraMap S Ω (t I)),
        mul_assoc]
      exact hS I _ (htz I)
    have h0 : algebraMap S F t₀ ≠ 0 := by
      have : Nontrivial S := (algebraMap S F).domain_nontrivial
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht₀m
    have : z = (algebraMap S F t₀)⁻¹ • (algebraMap S Ω t₀ * z) := by
      rw [Algebra.smul_def, map_inv₀, IsScalarTower.algebraMap_apply S F Ω,
        inv_mul_cancel_left₀ ((map_ne_zero _).mpr h0)]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
end GroundTheory.Heights₂.Heights.Kleiman
