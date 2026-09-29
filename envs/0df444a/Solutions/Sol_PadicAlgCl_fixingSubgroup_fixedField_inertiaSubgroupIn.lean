-- Prove2me | solution 1 for PadicAlgCl.fixingSubgroup_fixedField_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/355bfbfa-eba7-5dfc-88fe-9235fb891d96

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_fixingSubgroup_fixedField_inertiaSubgroupIn

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Pointwise
open IntermediateField

theorem solution (p : ℕ) [Fact p.Prime] :
    (IntermediateField.fixedField ((padicIntegers p).inertiaSubgroupIn ℚ_[p])).fixingSubgroup
      = (padicIntegers p).inertiaSubgroupIn ℚ_[p] := by
  classical
  set A : ValuationSubring (PadicAlgCl p) := padicIntegers p with hAdef
  set I : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) := A.inertiaSubgroupIn ℚ_[p] with hIdef

  have hD : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ A.decompositionSubgroup ℚ_[p] := by
    intro σ
    rw [MulAction.mem_stabilizer_iff]
    apply SetLike.ext
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, hAdef,
      mem_padicIntegers_iff, mem_padicIntegers_iff, nnnorm_padicAlgCl_algEquiv]

  have hmem : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      σ ∈ I ↔ ∀ a : A, ‖σ (a : PadicAlgCl p) - a‖₊ < 1 := by
    intro σ
    constructor
    · rintro ⟨d, hd, rfl⟩ a
      rw [SetLike.mem_coe, ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hd
      have h1 : d • IsLocalRing.residue A a = IsLocalRing.residue A a := by
        have := RingEquiv.congr_fun hd (IsLocalRing.residue A a)
        exact this
      rw [← IsLocalRing.ResidueField.residue_smul, IsLocalRing.residue] at h1
      have h2 : d • a - a ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq.mp h1
      rw [ValuationSubring.valuation_lt_one_iff,
        ← (Valuation.isEquiv_valuation_valuationSubring
          (Valued.v : Valuation (PadicAlgCl p) NNReal)).lt_one_iff_lt_one] at h2
      exact h2
    · intro h
      refine ⟨⟨σ, hD σ⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
      apply RingEquiv.ext
      intro r
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
      show (⟨σ, hD σ⟩ : A.decompositionSubgroup ℚ_[p]) • IsLocalRing.residue A a = IsLocalRing.residue A a
      rw [← IsLocalRing.ResidueField.residue_smul, IsLocalRing.residue]
      refine Ideal.Quotient.eq.mpr ?_
      rw [ValuationSubring.valuation_lt_one_iff,
        ← (Valuation.isEquiv_valuation_valuationSubring
          (Valued.v : Valuation (PadicAlgCl p) NNReal)).lt_one_iff_lt_one]
      exact h a

  have hclopen : ∀ a : A, IsClopen {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p | ‖σ (a : PadicAlgCl p) - a‖₊ < 1} := by
    intro a
    have hint : IsIntegral ℚ_[p] (a : PadicAlgCl p) := (Algebra.IsAlgebraic.isAlgebraic (a : PadicAlgCl p)).isIntegral
    haveI : FiniteDimensional ℚ_[p] ℚ_[p]⟮(a : PadicAlgCl p)⟯ := IntermediateField.adjoin.finiteDimensional hint
    have hU : IsOpen ((ℚ_[p]⟮(a : PadicAlgCl p)⟯).fixingSubgroup : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) :=
      IntermediateField.fixingSubgroup_isOpen _

    have hS : ∀ s ∈ {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p | ‖σ (a : PadicAlgCl p) - a‖₊ < 1},
        ∀ u ∈ (ℚ_[p]⟮(a : PadicAlgCl p)⟯).fixingSubgroup, s * u ∈ {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p | ‖σ (a : PadicAlgCl p) - a‖₊ < 1} := by
      intro s hs u hu
      simp only [IntermediateField.mem_fixingSubgroup_iff] at hu
      simp only [Set.mem_setOf_eq, AlgEquiv.mul_apply] at hs ⊢
      rw [hu _ (IntermediateField.mem_adjoin_simple_self ℚ_[p] (a : PadicAlgCl p))]
      exact hs

    have hSc : ∀ s ∉ {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p | ‖σ (a : PadicAlgCl p) - a‖₊ < 1},
        ∀ u ∈ (ℚ_[p]⟮(a : PadicAlgCl p)⟯).fixingSubgroup, s * u ∉ {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p | ‖σ (a : PadicAlgCl p) - a‖₊ < 1} :=
      fun s hs u hu hsu => hs (by simpa using hS (s * u) hsu u⁻¹ (Subgroup.inv_mem _ hu))
    have hopen : ∀ T : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
        (∀ s ∈ T, ∀ u ∈ (ℚ_[p]⟮(a : PadicAlgCl p)⟯).fixingSubgroup, s * u ∈ T) → IsOpen T := fun T hT => by
      refine isOpen_iff_forall_mem_open.mpr fun s hs =>
        ⟨s • ((ℚ_[p]⟮(a : PadicAlgCl p)⟯).fixingSubgroup : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)),
          ?_, hU.smul s, ?_⟩
      · rintro _ ⟨u, hu, rfl⟩
        exact hT s hs u hu
      · exact ⟨1, Subgroup.one_mem _, mul_one s⟩
    exact ⟨compl_compl {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p | ‖σ (a : PadicAlgCl p) - a‖₊ < 1} ▸ (hopen _ hSc).isClosed_compl, hopen _ hS⟩
  have hclosed : IsClosed (I : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) := by
    have heq : (I : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) =
        ⋂ a : A, {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p | ‖σ (a : PadicAlgCl p) - a‖₊ < 1} := by
      ext σ
      simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
      exact hmem σ
    rw [heq]
    exact isClosed_iInter fun a => (hclopen a).isClosed

  exact InfiniteGalois.fixingSubgroup_fixedField ⟨I, hclosed⟩

end S_PadicAlgCl_fixingSubgroup_fixedField_inertiaSubgroupIn
end P2MW
export P2MW.S_PadicAlgCl_fixingSubgroup_fixedField_inertiaSubgroupIn (solution)
