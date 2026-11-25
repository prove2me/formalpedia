-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.EigA.comm_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:19.123031+00:00
-- url     : https://prove2.me/submissions/e83118b7-9436-41c9-a1e7-40a01e9f8c60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
import Theorems.Thm_GlobalTheory_GelfandTrick_card_pairs_le
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.EigA
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.Rg.BcB.F.EigA
theorem _root_.solution (ρ : Representation ℂ G V) (J : Subgroup G) (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a)
    (hinv : ∀ a, τ (τ a) = a) (hdc : ∀ g : G, ∃ k₁ ∈ J, ∃ k₂ ∈ J, τ g = k₁ * g * k₂) (hJ : ∀ k ∈ J, τ k ∈ J)
    (α β : G) (R S : Finset G) (hR : ∀ γ ∈ R, ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * α * k₂)
    (hR' : ∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ J)
    (hS : ∀ γ ∈ S, ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * β * k₂)
    (hS' : ∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * β * k₂) → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ J)
    (x : V) (hx : ∀ k ∈ J, ρ k x = x) :
    ∑ γ ∈ R, ρ γ (∑ δ ∈ S, ρ δ x) = ∑ δ ∈ S, ρ δ (∑ γ ∈ R, ρ γ x) := by
  classical
  let f : G ⧸ J → V := fun c => ρ c.out x
  have hf : ∀ g : G, f (g : G ⧸ J) = ρ g x := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul J g
    simp only [f, hk, map_mul, Module.End.mul_apply, hx k k.2]
  have key : ∀ A B : Finset G, ∑ γ ∈ A, ρ γ (∑ δ ∈ B, ρ δ x)
      = ∑ p ∈ A ×ˢ B, f ((p.1 * p.2 : G) : G ⧸ J) := fun A B => by
    rw [Finset.sum_product]
    simp only [hf, map_sum, map_mul, Module.End.mul_apply]
  rw [key, key]
  let T : Finset (G ⧸ J) := (R ×ˢ S).image (fun p => ((p.1 * p.2 : G) : G ⧸ J)) ∪
    (S ×ˢ R).image (fun p => ((p.1 * p.2 : G) : G ⧸ J))
  rw [← Finset.sum_fiberwise_of_maps_to' (s := R ×ˢ S) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ J))
      (fun p hp => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)) f,
    ← Finset.sum_fiberwise_of_maps_to' (s := S ×ˢ R) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ J))
      (fun p hp => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)) f]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_const, Finset.sum_const]
  congr 1
  apply le_antisymm
  · convert GlobalTheory.GelfandTrick.card_pairs_le J τ hmul hinv hdc hJ α β R S hR hR' hS hS' c
  · convert GlobalTheory.GelfandTrick.card_pairs_le J τ hmul hinv hdc hJ β α S R hS hS' hR hR' c
end PositivityTheory.Rg.BcB.F.EigA
