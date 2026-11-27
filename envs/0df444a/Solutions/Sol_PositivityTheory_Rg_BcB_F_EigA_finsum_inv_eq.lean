-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.EigA.finsum_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:21:09.805504+00:00
-- url     : https://prove2.me/submissions/3e0a75bc-32bd-4316-8833-4bee4c533b09

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_TraceMulOfFinrankOne
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_out_mk_inv
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
open scoped Pointwise
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.EigA
variable {G : Type} [Group G]
namespace PositivityTheory.Rg.BcB.F.EigA
theorem _root_.solution {K : Subgroup G} (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a)
    (hdc : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) (hK : ∀ k ∈ K, τ k ∈ K)
    {M : Type} [AddCommMonoid M] (F : G → M) (hF : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ x, F (k₁ * x * k₂) = F x) :
    ∑ᶠ q : G ⧸ K, F (q.out)⁻¹ = ∑ᶠ q : G ⧸ K, F q.out := by
  have hone : τ 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact (mul_eq_left.mp h.symm)
  have hτinv : ∀ a, τ a⁻¹ = (τ a)⁻¹ := fun a => by
    have h := hmul a a⁻¹
    rw [mul_inv_cancel, hone] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  let σ : G → G := fun x => τ x⁻¹
  have hσmul : ∀ a b, σ (a * b) = σ a * σ b := by
    intro a b
    simp only [σ, mul_inv_rev, hmul]
  have hσσ : ∀ a, σ (σ a) = a := by
    intro a
    simp only [σ, hτinv, inv_inv, hinv]
  have hσK : ∀ k ∈ K, σ k ∈ K := fun k hk => hK _ (K.inv_mem hk)
  have hFτ : ∀ x, F (τ x) = F x := fun x => by
    obtain ⟨k₁, h₁, k₂, h₂, e⟩ := hdc x
    rw [e, hF _ h₁ _ h₂]
  have hFr : ∀ x, ∀ k ∈ K, F (x * k) = F x := fun x k hk => by
    simpa using hF 1 K.one_mem k hk x
  let s : G ⧸ K → G ⧸ K := fun q => ((σ q.out : G) : G ⧸ K)
  have hs : ∀ q, s (s q) = q := by
    intro q
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (σ q.out)
    show ((σ ((σ q.out : G) : G ⧸ K).out : G) : G ⧸ K) = q
    rw [hk, hσmul, hσσ, QuotientGroup.mk_mul_of_mem _ (hσK _ k.2), QuotientGroup.out_eq']
  let e : G ⧸ K ≃ G ⧸ K := ⟨s, s, hs, hs⟩
  conv_rhs => rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  show F (q.out)⁻¹ = F ((σ q.out : G) : G ⧸ K).out
  rw [out_mk_inv K F hFr]
  show F (q.out)⁻¹ = F (τ (q.out)⁻¹)
  rw [hFτ]
end PositivityTheory.Rg.BcB.F.EigA
