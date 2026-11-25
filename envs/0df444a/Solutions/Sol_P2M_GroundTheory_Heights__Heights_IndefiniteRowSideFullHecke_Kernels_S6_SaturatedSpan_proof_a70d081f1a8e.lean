-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_SaturatedSpan_proof_a70d081f1a8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:32:42.657798+00:00
-- url     : https://prove2.me/submissions/72e29b55-a713-4ee8-9704-95724b809cc9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6.SaturatedSpan
theorem _root_.solution : S6.SaturatedSpan.Statement := by
  intro K _ _ M _ _ _ n ψ hψ G hsat
  obtain ⟨S, hS, hli⟩ := exists_set_linearIndependent_of_isDomain (𝓞 K) G
  rw [← Module.finrank_eq_rank] at hS
  obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hS
  let f : Fin (Module.finrank (𝓞 K) G) → G := fun i ↦ (e.symm i : G)
  have hf : LinearIndependent (𝓞 K) f := hli.comp _ e.symm.injective
  let φ : G →ₗ[𝓞 K] (Fin n → K) := ψ ∘ₗ G.subtype
  have hφ : Function.Injective φ := hψ.comp Subtype.val_injective
  let b : Fin (Module.finrank (𝓞 K) G) → Fin n → K := φ ∘ f
  have hbO : LinearIndependent (𝓞 K) b := hf.map' φ (LinearMap.ker_eq_bot.mpr hφ)
  have hb : LinearIndependent K b := (LinearIndependent.iff_fractionRing (𝓞 K) K).mp hbO
  refine ⟨b, hb, ?_⟩
  have hspanO : ∀ c : Fin (Module.finrank (𝓞 K) G) → 𝓞 K,
      φ (∑ j, c j • f j) ∈ Submodule.span K (Set.range b) := by
    intro c
    rw [map_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    rw [map_smul, ← algebraMap_smul K (c j)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.mem_inf.mpr ⟨LinearMap.mem_range_self ψ x, ?_⟩
    have hnot : ¬ LinearIndependent (𝓞 K)
        (Fin.cons ⟨x, hx⟩ f : Fin (Module.finrank (𝓞 K) G + 1) → G) := by
      intro h
      have := h.fintype_card_le_finrank
      simp at this
    obtain ⟨s, hs0, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnot
    rw [Fin.sum_univ_succ] at hs0
    simp only [Fin.cons_zero, Fin.cons_succ] at hs0
    have ht : s 0 ≠ 0 := by
      intro h0
      rw [h0, zero_smul, zero_add] at hs0
      have hz := Fintype.linearIndependent_iff.mp hf (fun j ↦ s j.succ) hs0
      refine hi ?_
      cases i using Fin.cases with
      | zero => exact h0
      | succ j => exact hz j
    have key : s 0 • (⟨x, hx⟩ : G) = ∑ j, (-s j.succ) • f j := by
      simp only [neg_smul, Finset.sum_neg_distrib]
      exact eq_neg_of_add_eq_zero_left hs0
    have hmem := hspanO (fun j ↦ -s j.succ)
    rw [← key, map_smul] at hmem
    have hK : algebraMap (𝓞 K) K (s 0) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ht
    rw [← algebraMap_smul K (s 0)] at hmem
    have h2 := Submodule.smul_mem _ (algebraMap (𝓞 K) K (s 0))⁻¹ hmem
    rw [smul_smul, inv_mul_cancel₀ hK, one_smul] at h2
    exact h2
  · rintro y hy
    obtain ⟨⟨x, rfl⟩, hy⟩ := Submodule.mem_inf.mp hy
    have hy' : ψ x ∈ Submodule.span K (Set.range b) := hy
    obtain ⟨κ, hκ⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy'
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples (𝓞 K)⁰ Finset.univ κ
    choose a ha using fun j ↦ ht j (Finset.mem_univ j)
    have htx : (t : 𝓞 K) • x ∈ G := by
      have heq : ψ ((t : 𝓞 K) • x) = ψ (∑ j, a j • (f j : M)) := by
        rw [map_smul, ← hκ, map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [map_smul, ← algebraMap_smul K (a j), ha j, smul_assoc]
        rfl
      rw [hψ heq]
      exact Submodule.sum_mem _ fun j _ ↦ G.smul_mem _ (f j).2
    exact ⟨x, hsat _ x (nonZeroDivisors.coe_ne_zero t) htx, rfl⟩
end S6.SaturatedSpan
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
