-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_proof_e53ace07c4b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:03:52.793409+00:00
-- url     : https://prove2.me/submissions/cd747b83-f7e5-43d0-97a7-98a392773684

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsVeryAmpleZFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZChartSpan
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_prod_mem_pow_1dbdeee6f1d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZChartSpan_exists_coeff_of_mem_twist_939e653bd620
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_xProd_ne_zero_5c3b01ddff8c


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
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZChartSpan
theorem _root_.solution : VeryAmpleZChartSpan.Statement := by
  intro S _ Ω _ _ N x E _ _ _ _ F H r h hh I J g hg e he
  have hJ : xProd J ∈ (H.pow J.1.card).sub I := prod_mem_pow H I hh J.1
  have h0 : xProd J ≠ 0 := AmpleAffineGen.xProd_ne_zero J
  have memB : ∀ {a : Ω}, a ∈ ampleChart H J.1.card (xProd J) I →
      a ∈ AmpleAffineGen.ampleSubalg H J.1.card (xProd J) I hJ := fun ha => ha
  change e ∈ Submodule.span S _ at he
  induction he using Submodule.span_induction with
  | mem e he =>
    obtain ⟨n, hn⟩ := he
    obtain ⟨γ, hγ, hz⟩ := exists_coeff_of_mem_twist F _ I g hg hn
    have hp : xProd J ^ n ≠ 0 := pow_ne_zero n h0
    refine ⟨fun y => γ y / xProd J ^ n, fun y hy => ⟨n, ?_⟩, ?_⟩
    · rw [div_mul_cancel₀ _ hp]; exact hγ y hy
    · have he' : e = (xProd J ^ n)⁻¹ • (xProd J ^ n • e) := by
        rw [smul_smul, inv_mul_cancel₀ hp, one_smul]
      rw [he', hz, Finset.smul_sum]
      exact Finset.sum_congr rfl fun y _ => by
        show _ = (γ y / xProd J ^ n) • y
        rw [smul_smul, div_eq_inv_mul]
  | zero =>
    refine ⟨0, fun _ _ => ⟨0, ?_⟩, by simp⟩
    rw [Pi.zero_apply, zero_mul]; exact Submodule.zero_mem _
  | add e e' _ _ ih ih' =>
    obtain ⟨β, hβ, rfl⟩ := ih
    obtain ⟨β', hβ', rfl⟩ := ih'
    refine ⟨β + β', fun y hy => Subalgebra.add_mem _ (memB (hβ y hy)) (memB (hβ' y hy)), ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [Pi.add_apply, add_smul]
  | smul s e _ ih =>
    obtain ⟨β, hβ, rfl⟩ := ih
    refine ⟨fun y => algebraMap S Ω s * β y,
      fun y hy => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ s) (memB (hβ y hy)), ?_⟩
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [← smul_assoc, Algebra.smul_def]
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZChartSpan
