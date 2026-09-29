-- Prove2me | solution 1 for ValuationSubring.exists_algEquiv_forall_mem_iff_of_isGalois_infinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/32985648-df5a-5cf1-affa-efb36cce6798

import Mathlib
import Theorems.Thm_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois_infinite

set_option autoImplicit false

namespace ValuationSubring
p2m_export "ValuationSubring" "comap mem_comap algebraMap_apply one_mem valuation exists_algEquiv_forall_mem_iff_of_isGalois"
namespace InfiniteConjugacy
p2m_open "ValuationSubring"

open scoped Topology Pointwise

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

theorem isClosed_of_mul_mem_iff (H : Subgroup (F ≃ₐ[E] F)) (hH : IsOpen (H : Set (F ≃ₐ[E] F)))
    (D : Set (F ≃ₐ[E] F)) (hD : ∀ σ : F ≃ₐ[E] F, ∀ h ∈ H, σ * h ∈ D ↔ σ ∈ D) : IsClosed D := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun h => σ * h) '' (H : Set (F ≃ₐ[E] F)), ?_, isOpenMap_mul_left σ _ hH,
    ⟨1, H.one_mem, mul_one σ⟩⟩
  rintro _ ⟨h, hh, rfl⟩ hmem
  exact hσ ((hD σ h hh).mp hmem)

variable (O' O'' : ValuationSubring F)

def transportAt (x : F) : Set (F ≃ₐ[E] F) := {σ | σ x ∈ O'' ↔ x ∈ O'}

theorem isClosed_transportAt [Algebra.IsAlgebraic E F] (x : F) :
    IsClosed (transportAt (E := E) O' O'' x) := by
  haveI : FiniteDimensional E (IntermediateField.adjoin E {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  refine isClosed_of_mul_mem_iff (IntermediateField.adjoin E {x}).fixingSubgroup
    (IntermediateField.fixingSubgroup_isOpen _) _ fun σ h hh => ?_
  have hx : h x = x :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hh x (IntermediateField.mem_adjoin_simple_self E x)
  simp only [transportAt, Set.mem_setOf_eq, AlgEquiv.mul_apply, hx]

theorem nonempty_iInter_transportAt [IsGalois E F] (O : ValuationSubring E)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O)
    (hO'' : ∀ x : E, algebraMap E F x ∈ O'' ↔ x ∈ O) (s : Finset F) :
    (⋂ x ∈ s, transportAt (E := E) O' O'' x).Nonempty := by
  classical

  let L := (FiniteGaloisIntermediateField.adjoin E (↑s : Set F)).toIntermediateField
  have hsL : (↑s : Set F) ⊆ L := FiniteGaloisIntermediateField.subset_adjoin E (↑s : Set F)

  obtain ⟨τ, hτ⟩ := ValuationSubring.exists_algEquiv_forall_mem_iff_of_isGalois (E := E) (F := L) O
    (O'.comap (algebraMap L F)) (O''.comap (algebraMap L F))
    (fun x => by rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]; exact hO x)
    (fun x => by rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]; exact hO'' x)
  refine ⟨τ.liftNormal F, Set.mem_iInter₂.mpr fun x hx => ?_⟩
  have hxL : x ∈ L := hsL (Finset.mem_coe.mpr hx)
  have h1 : τ.liftNormal F x = algebraMap L F (τ ⟨x, hxL⟩) := by
    simpa using AlgEquiv.liftNormal_commutes τ F ⟨x, hxL⟩
  show τ.liftNormal F x ∈ O'' ↔ x ∈ O'
  rw [h1]
  simpa [ValuationSubring.mem_comap] using hτ ⟨x, hxL⟩

end ValuationSubring.InfiniteConjugacy

open ValuationSubring.InfiniteConjugacy in

theorem solution
    {E F : Type*} [Field E] [Field F] [Algebra E F] [IsGalois E F]
    (O : ValuationSubring E)
    (O' O'' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O)
    (hO'' : ∀ x : E, algebraMap E F x ∈ O'' ↔ x ∈ O) :
    ∃ σ : F ≃ₐ[E] F, ∀ x : F, σ x ∈ O'' ↔ x ∈ O' := by
  classical
  let t : Finset F → Set (F ≃ₐ[E] F) := fun s => ⋂ x ∈ s, transportAt (E := E) O' O'' x
  have hdir : Directed (fun a b => a ⊇ b) t := by
    intro s s'
    refine ⟨s ∪ s', ?_, ?_⟩ <;>
      exact Set.biInter_subset_biInter_left (by intro x hx; simp_all)
  have hne : ∀ s, (t s).Nonempty := nonempty_iInter_transportAt O' O'' O hO hO''
  have hclosed : ∀ s, IsClosed (t s) := fun s =>
    isClosed_biInter fun x _ => isClosed_transportAt O' O'' x
  have hcompact : ∀ s, IsCompact (t s) := fun s => (hclosed s).isCompact
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne
    hcompact hclosed
  refine ⟨σ, fun x => ?_⟩
  have := Set.mem_iInter.mp hσ {x}
  simpa [t, transportAt] using this

end S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois_infinite
end P2MW
export P2MW.S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_isGalois_infinite (solution)
