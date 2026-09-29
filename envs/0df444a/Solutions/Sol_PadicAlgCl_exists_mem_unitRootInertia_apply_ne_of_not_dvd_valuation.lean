-- Prove2me | solution 1 for PadicAlgCl.exists_mem_unitRootInertia_apply_ne_of_not_dvd_valuation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fc69cfbb-f26a-5fc0-99f0-13df49226e14

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_GaloisRep_OrdinaryUnitClasses
import Theorems.Thm_PadicAlgCl_exists_mem_inertiaSubgroupIn_apply_ne_of_forall_pow_eq_of_not_dvd_valuation
import Theorems.Thm_PadicAlgCl_fixingSubgroup_fixedField_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_mem_unitRootInertia_apply_ne_of_not_dvd_valuation
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO"

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation
open scoped IntermediateField

theorem solution
    (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (hx : ¬ (p : ℤ) ∣ Padic.valuation x)
    (γ : PadicAlgCl p) (hγ : γ ^ p = algebraMap ℚ_[p] (PadicAlgCl p) x) :
    ∃ τ ∈ ResidualGaloisRep.unitRootInertia p, ResidualGaloisRep.localAut p τ γ ≠ γ := by
  classical

  let Γ := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p
  let I : Subgroup Γ := (padicIntegers p).inertiaSubgroupIn ℚ_[p]

  have hstab_open : ∀ z : PadicAlgCl p, IsOpen ((MulAction.stabilizer Γ z : Subgroup Γ) : Set Γ) := by
    intro z
    have hint : IsIntegral ℚ_[p] z := Algebra.IsIntegral.isIntegral z
    haveI : FiniteDimensional ℚ_[p] ℚ_[p]⟮z⟯ := IntermediateField.adjoin.finiteDimensional hint
    apply Subgroup.isOpen_mono (H₁ := ℚ_[p]⟮z⟯.fixingSubgroup)
    · intro τ hτ
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ z
        (IntermediateField.mem_adjoin_simple_self _ z)
    · exact IntermediateField.fixingSubgroup_isOpen _
  have hstab_closed : ∀ z : PadicAlgCl p, IsClosed {τ : Γ | τ z = z} := by
    intro z
    have : {τ : Γ | τ z = z} = ((MulAction.stabilizer Γ z : Subgroup Γ) : Set Γ) := by
      ext τ; simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_setOf_eq]; rfl
    rw [this]
    exact Subgroup.isClosed_of_isOpen _ (hstab_open z)
  have hmove_closed : ∀ z : PadicAlgCl p, IsClosed {τ : Γ | τ z ≠ z} := by
    intro z
    have : {τ : Γ | τ z ≠ z} = (((MulAction.stabilizer Γ z : Subgroup Γ) : Set Γ))ᶜ := by
      ext τ; simp only [Set.mem_compl_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_setOf_eq]; rfl
    rw [this]
    exact (hstab_open z).isClosed_compl

  have hI_closed : IsClosed (I : Set Γ) := by
    have h := PadicAlgCl.fixingSubgroup_fixedField_inertiaSubgroupIn p
    show IsClosed (((padicIntegers p).inertiaSubgroupIn ℚ_[p] : Subgroup Γ) : Set Γ)
    rw [← h]
    exact InfiniteGalois.fixingSubgroup_isClosed _

  let B : Set (PadicAlgCl p) := {β | ‖β‖₊ = 1 ∧ ∀ τ : Γ, τ ∈ I → τ (β ^ p) = β ^ p}

  let C : Finset B → Set Γ := fun s =>
    (I : Set Γ) ∩ {τ | ∀ ζ : PadicAlgCl p, ζ ^ p = 1 → τ ζ = ζ} ∩ {τ | ∀ β ∈ s, τ (β : PadicAlgCl p) = β} ∩
      {τ | τ γ ≠ γ}
  have hC_closed : ∀ s, IsClosed (C s) := by
    intro s
    refine ((hI_closed.inter ?_).inter ?_).inter (hmove_closed γ)
    · have : {τ : Γ | ∀ ζ : PadicAlgCl p, ζ ^ p = 1 → τ ζ = ζ} = ⋂ ζ ∈ {ζ : PadicAlgCl p | ζ ^ p = 1}, {τ : Γ | τ ζ = ζ} := by
        ext τ; simp
      rw [this]
      exact isClosed_biInter fun ζ _ => hstab_closed ζ
    · have : {τ : Γ | ∀ β ∈ s, τ (β : PadicAlgCl p) = β} = ⋂ β ∈ s, {τ : Γ | τ (β : PadicAlgCl p) = β} := by
        ext τ; simp
      rw [this]
      exact isClosed_biInter fun β _ => hstab_closed (β : PadicAlgCl p)
  have hC_dir : Directed (· ⊇ ·) C := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · rintro τ ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨⟨⟨h1, h2⟩, fun β hβ => h3 β (Finset.mem_union_left _ hβ)⟩, h4⟩
    · rintro τ ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨⟨⟨h1, h2⟩, fun β hβ => h3 β (Finset.mem_union_right _ hβ)⟩, h4⟩
  have hC_ne : ∀ s, (C s).Nonempty := by
    intro s

    let e := s.equivFin
    let βf : Fin s.card → PadicAlgCl p := fun i => ((e.symm i : B) : PadicAlgCl p)
    let uf : Fin s.card → PadicAlgCl p := fun i => βf i ^ p
    have hu : ∀ i, ‖uf i‖₊ = 1 := by
      intro i
      simp only [uf, βf, nnnorm_pow, ((e.symm i : B) : B).2.1, one_pow]
    have huI : ∀ i, ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], τ (uf i) = uf i :=
      fun i τ hτ => ((e.symm i : B) : B).2.2 τ hτ
    obtain ⟨τ, hτI, hτζ, hτβ, hτγ⟩ :=
      PadicAlgCl.exists_mem_inertiaSubgroupIn_apply_ne_of_forall_pow_eq_of_not_dvd_valuation p uf βf hu huI
        (fun _ => rfl) x hx γ hγ
    refine ⟨τ, ⟨⟨hτI, hτζ⟩, fun β hβ => ?_⟩, hτγ⟩
    have := hτβ (e ⟨β, hβ⟩)
    simpa [βf] using this
  haveI : Nonempty (Finset B) := ⟨∅⟩
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hC_dir hC_ne
    (fun s => (hC_closed s).isCompact) hC_closed
  rw [Set.mem_iInter] at hτ
  have h0 := hτ ∅
  refine ⟨τ, ⟨h0.1.1.1, h0.1.1.2, fun β hβ1 hβI => ?_⟩, h0.2⟩
  have hβB : β ∈ B := ⟨hβ1, fun τ' hτ' => hβI τ' hτ'⟩
  exact (hτ {⟨β, hβB⟩}).1.2 ⟨β, hβB⟩ (Finset.mem_singleton_self _)

end S_PadicAlgCl_exists_mem_unitRootInertia_apply_ne_of_not_dvd_valuation
end P2MW
export P2MW.S_PadicAlgCl_exists_mem_unitRootInertia_apply_ne_of_not_dvd_valuation (solution)
