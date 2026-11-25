-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.EigA.reps_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:32:19.813123+00:00
-- url     : https://prove2.me/submissions/f0d3f321-1295-47e6-a8e1-c4cfa7f2d041

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_mem_stabK
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
theorem _root_.solution (K : Subgroup G) (g : G) [Fintype (K ⧸ stabK K g)] :
    (∀ γ ∈ reps K g, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * g * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) → ∃! γ, γ ∈ reps K g ∧ γ⁻¹ * x ∈ K := by
  classical
  constructor
  · intro γ hγ
    unfold reps at hγ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hγ
    exact ⟨_, (q.out : K).2, 1, K.one_mem, by rw [mul_one]⟩
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    let q : K ⧸ stabK K g := ((⟨k₁, hk₁⟩ : K) : K ⧸ stabK K g)
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (stabK K g) (⟨k₁, hk₁⟩ : K)
    have hhK : g⁻¹ * ((h : K) : G) * g ∈ K := mem_stabK.1 h.2
    have hx1 : (((q.out : K) : G) * g)⁻¹ * (k₁ * g * k₂) ∈ K := by
      have e : (((q.out : K) : G) * g)⁻¹ * (k₁ * g * k₂) = (g⁻¹ * ((h : K) : G) * g)⁻¹ * k₂ := by
        rw [show q.out = (⟨k₁, hk₁⟩ : K) * (h : K) from hh]
        simp only [Subgroup.coe_mul]
        group
      rw [e]
      exact K.mul_mem (K.inv_mem hhK) hk₂
    refine ⟨((q.out : K) : G) * g, ⟨by unfold reps; exact Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩, hx1⟩, ?_⟩
    rintro γ ⟨hγ, hγx⟩
    unfold reps at hγ
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hγ
    have hmem : g⁻¹ * (((q'.out : K)⁻¹ * q.out : K) : G) * g ∈ K := by
      have e : g⁻¹ * (((q'.out : K)⁻¹ * q.out : K) : G) * g =
          ((((q'.out : K) : G) * g)⁻¹ * (k₁ * g * k₂)) * ((((q.out : K) : G) * g)⁻¹ * (k₁ * g * k₂))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact K.mul_mem hγx (K.inv_mem hx1)
    have hqq : q' = q := by
      rw [← QuotientGroup.out_eq' q', ← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 (mem_stabK.2 hmem)
    rw [hqq]
end PositivityTheory.Rg.BcB.F.EigA
