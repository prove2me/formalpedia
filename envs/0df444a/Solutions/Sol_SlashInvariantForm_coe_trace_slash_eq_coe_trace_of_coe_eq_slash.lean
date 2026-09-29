-- Prove2me | solution 1 for SlashInvariantForm.coe_trace_slash_eq_coe_trace_of_coe_eq_slash
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/574ff315-6413-5aee-ba14-95eff50911a6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_SlashInvariantForm_coe_trace_slash_eq_coe_trace_of_coe_eq_slash

set_option autoImplicit false

open scoped MatrixGroups ModularForm
open UpperHalfPlane

namespace TraceEquiv

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} (A W : GL (Fin 2) ℝ)
  (hA : ∀ x ∈ 𝒢, A * x * A⁻¹ ∈ 𝒢) (hW : ∀ x ∈ ℋ, W * x * W⁻¹ ∈ ℋ) (hW' : ∀ x ∈ ℋ, W⁻¹ * x * W ∈ ℋ)
  (hAW : A * W⁻¹ ∈ ℋ)

include hW hAW in
theorem mem_fwd (r : ℋ) : W * (r : GL (Fin 2) ℝ) * A⁻¹ ∈ ℋ := by
  have h1 : W * (r : GL (Fin 2) ℝ) * W⁻¹ ∈ ℋ := hW r r.2
  have h2 : W * A⁻¹ ∈ ℋ := by
    have := ℋ.inv_mem hAW
    rwa [mul_inv_rev, inv_inv] at this
  have := ℋ.mul_mem h1 h2
  rwa [mul_assoc, inv_mul_cancel_left] at this

include hW' hAW in
theorem mem_bwd (r : ℋ) : W⁻¹ * (r : GL (Fin 2) ℝ) * A ∈ ℋ := by
  have h1 : W⁻¹ * (r : GL (Fin 2) ℝ) * W ∈ ℋ := hW' r r.2
  have h2 : W⁻¹ * (A * W⁻¹) * W ∈ ℋ := hW' _ hAW
  rw [mul_assoc, inv_mul_cancel_right] at h2
  have := ℋ.mul_mem h1 h2
  rwa [mul_assoc, mul_inv_cancel_left] at this

def fwd (r : ℋ) : ℋ := ⟨W * (r : GL (Fin 2) ℝ) * A⁻¹, mem_fwd A W hW hAW r⟩

def bwd (r : ℋ) : ℋ := ⟨W⁻¹ * (r : GL (Fin 2) ℝ) * A, mem_bwd A W hW' hAW r⟩

include hA in
theorem fwd_rel (a b : ℋ) (h : QuotientGroup.leftRel (𝒢.subgroupOf ℋ) a b) :
    QuotientGroup.leftRel (𝒢.subgroupOf ℋ) (fwd A W hW hAW a) (fwd A W hW hAW b) := by
  rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
  have : ((fwd A W hW hAW a)⁻¹ * fwd A W hW hAW b : ℋ) =
      (A * ((a : GL (Fin 2) ℝ)⁻¹ * b) * A⁻¹ : GL (Fin 2) ℝ) := by
    simp only [fwd, Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev, inv_inv]
    group
  rw [this]
  exact hA _ (by simpa using h)

theorem bwd_rel (hA' : ∀ x ∈ 𝒢, A⁻¹ * x * A ∈ 𝒢) (a b : ℋ) (h : QuotientGroup.leftRel (𝒢.subgroupOf ℋ) a b) :
    QuotientGroup.leftRel (𝒢.subgroupOf ℋ) (bwd A W hW' hAW a) (bwd A W hW' hAW b) := by
  rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
  have : ((bwd A W hW' hAW a)⁻¹ * bwd A W hW' hAW b : ℋ) =
      (A⁻¹ * ((a : GL (Fin 2) ℝ)⁻¹ * b) * A : GL (Fin 2) ℝ) := by
    simp only [bwd, Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev, inv_inv]
    group
  rw [this]
  exact hA' _ (by simpa using h)

def quotEquiv (hA' : ∀ x ∈ 𝒢, A⁻¹ * x * A ∈ 𝒢) :
    ℋ ⧸ 𝒢.subgroupOf ℋ ≃ ℋ ⧸ 𝒢.subgroupOf ℋ where
  toFun := Quotient.map' (fwd A W hW hAW) (fwd_rel A W hA hW hAW)
  invFun := Quotient.map' (bwd A W hW' hAW) (bwd_rel A W hW' hAW hA')
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h r =>
      show Quotient.mk _ (bwd A W hW' hAW (fwd A W hW hAW r)) = Quotient.mk _ r
      congr 1
      ext1
      simp only [bwd, fwd]
      group
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h r =>
      show Quotient.mk _ (fwd A W hW hAW (bwd A W hW' hAW r)) = Quotient.mk _ r
      congr 1
      ext1
      simp only [bwd, fwd]
      group

end TraceEquiv

open TraceEquiv in
theorem solution
    {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex ℋ] {k : ℤ}
    {F G : Type*} [FunLike F UpperHalfPlane ℂ] [FunLike G UpperHalfPlane ℂ]
    [SlashInvariantFormClass F 𝒢 k] [SlashInvariantFormClass G 𝒢 k]
    (f : F) (g : G) (A W : GL (Fin 2) ℝ) (hg : (⇑g : UpperHalfPlane → ℂ) = (⇑f : UpperHalfPlane → ℂ) ∣[k] A)
    (hA : ∀ x ∈ 𝒢, A * x * A⁻¹ ∈ 𝒢) (hA' : ∀ x ∈ 𝒢, A⁻¹ * x * A ∈ 𝒢)
    (hW : ∀ x ∈ ℋ, W * x * W⁻¹ ∈ ℋ) (hW' : ∀ x ∈ ℋ, W⁻¹ * x * W ∈ ℋ) (hAW : A * W⁻¹ ∈ ℋ) :
    (⇑(SlashInvariantForm.trace ℋ f) : UpperHalfPlane → ℂ) ∣[k] W = ⇑(SlashInvariantForm.trace ℋ g) := by
  classical
  letI := Fintype.ofFinite (ℋ ⧸ 𝒢.subgroupOf ℋ)
  rw [SlashInvariantForm.coe_trace, SlashInvariantForm.coe_trace, SlashAction.sum_slash]
  refine (Fintype.sum_equiv (quotEquiv A W hA hW hW' hAW hA') _ _ fun q => ?_).symm
  induction q using Quotient.inductionOn with
  | h r =>
    show SlashInvariantForm.quotientFunc g ⟦r⟧ = SlashInvariantForm.quotientFunc f ⟦fwd A W hW hAW r⟧ ∣[k] W
    rw [SlashInvariantForm.quotientFunc_mk, SlashInvariantForm.quotientFunc_mk, hg, ← SlashAction.slash_mul,
      ← SlashAction.slash_mul]
    congr 1
    simp only [fwd, mul_inv_rev, inv_inv]
    group

end S_SlashInvariantForm_coe_trace_slash_eq_coe_trace_of_coe_eq_slash
end P2MW
export P2MW.S_SlashInvariantForm_coe_trace_slash_eq_coe_trace_of_coe_eq_slash (solution)
