-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_idealMod_zeroIdeal_mul_le_be5ef0c4f392
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:14.865863+00:00
-- url     : https://prove2.me/submissions/697f2e0f-a1a1-4da1-b08b-2ddfef022a02

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_homogeneousComponent_mul_mem_420e5fb24bd2

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
open GroundTheory.Heights₂.Heights.Kleiman.StepThree GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
theorem _root_.solution (D : SubSystem S x Ω) (σ : Ω) (I : Chart x) :
    idealMod (x := x) (zeroIdeal D σ) I * D.sub I ≤ Submodule.span (chartRing S x I) {σ} := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [Submodule.mul_le]
  intro a ha δ hδ
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨f, s, e, hf, hs, hfe, hse, rfl⟩ := ha
    have h := homogeneousComponent_mul_mem D σ I hi hf e δ hδ
    rw [homogeneousComponent_of_mem hfe, if_pos rfl] at h
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
    have hs0 := eval_ne_zero_of_mem_monos I hs
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨x i ^ e / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow i e, hse,
      by rw [map_pow, aeval_X]⟩ * t, ?_⟩
    rw [chartRing_smul_def, Subalgebra.coe_mul,
      show aeval x f / aeval x s * δ = aeval x f * δ / aeval x s by ring, ← ht, chartRing_smul_def]
    field_simp
    try ring
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r ha
end GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
