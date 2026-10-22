-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P23.essentialSelfAdjoint_of_denseRestriction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T13:30:07.846394+00:00
-- url     : https://prove2.me/submissions/2914bdb0-6cdb-4193-b2d4-e73e92220c2f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P23

set_option autoImplicit false

namespace C206469fAux

open LinearPMap

/-- The closure of a densely defined closable operator is a formal adjoint partner of its adjoint. -/
theorem closure_isFormalAdjoint_adjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →ₗ.[ℂ] H) (hB : Dense (B.domain : Set H)) (hc : B.IsClosable) :
    B.closure.IsFormalAdjoint (B†) := by
  intro x y
  let t : Set (H × H) := {p | inner ℂ p.2 (y : H) = inner ℂ p.1 ((B†) y)}
  have ht : IsClosed t :=
    isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)
  have hsub : (B.graph : Set (H × H)) ⊆ t := by
    intro p hp
    rcases (mem_graph_iff B).mp hp with ⟨z, hz1, hz2⟩
    show inner ℂ p.2 (y : H) = inner ℂ p.1 ((B†) y)
    rw [← hz1, ← hz2]
    exact (adjoint_isFormalAdjoint hB).symm z y
  have hcl : (B.closure.graph : Set (H × H)) ⊆ t := by
    rw [← hc.graph_closure_eq_closure_graph, Submodule.topologicalClosure_coe]
    exact closure_minimal hsub ht
  have hx : ((x : H), B.closure x) ∈ B.closure.graph := (mem_graph_iff _).mpr ⟨x, rfl, rfl⟩
  exact hcl hx

theorem closure_eq_self_of_isClosed
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (C : H →ₗ.[ℂ] H) (hC : C.IsClosed) : C.closure = C := by
  apply eq_of_eq_graph
  rw [← hC.isClosable.graph_closure_eq_closure_graph]
  exact IsClosed.submodule_topologicalClosure_eq hC

end C206469fAux

open QAlgorithms.Papers.Independent.Frontier30.P23 LinearPMap in
theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (D1 : Submodule ℂ H)
    (hD1 : D1 ≤ A.domain) (hDense : Dense (D1 : Set H))
    (hSymmetric : A.IsFormalAdjoint A)
    (hRestrictionClosable : (A.domRestrict D1).IsClosable)
    (hRestrictionSelfAdjoint : IsSelfAdjoint (A.domRestrict D1).closure) :
    A.IsClosable ∧ IsSelfAdjoint A.closure ∧
      A.closure = (A.domRestrict D1).closure := by
  set B := A.domRestrict D1 with hBdef
  have hBdom : B.domain = D1 := by
    rw [hBdef, LinearPMap.domRestrict_domain]
    exact inf_eq_left.mpr hD1
  have hBdense : Dense (B.domain : Set H) := by rw [hBdom]; exact hDense
  have hAdense : Dense (A.domain : Set H) := hDense.mono hD1
  have hAle : A ≤ A† := LinearPMap.IsFormalAdjoint.le_adjoint hAdense hSymmetric
  have hAcl : A.IsClosable :=
    (LinearPMap.adjoint_isClosed hAdense).isClosable.leIsClosable hAle
  have hBA : B.IsFormalAdjoint A := by
    intro x y
    have hx : (x : H) ∈ A.domain := (show (x : H) ∈ D1 ⊓ A.domain from x.2).2
    rw [show B x = A ⟨x, hx⟩ from LinearPMap.domRestrict_apply rfl]
    exact hSymmetric ⟨x, hx⟩ y
  have hA_le_Badj : A ≤ B† := LinearPMap.IsFormalAdjoint.le_adjoint hBdense hBA
  have hBbar_dense : Dense (B.closure.domain : Set H) := hRestrictionSelfAdjoint.dense_domain
  have hBadj_le : B† ≤ B.closure† :=
    LinearPMap.IsFormalAdjoint.le_adjoint hBbar_dense
      (C206469fAux.closure_isFormalAdjoint_adjoint B hBdense hRestrictionClosable)
  have hSA : B.closure† = B.closure := LinearPMap.isSelfAdjoint_def.mp hRestrictionSelfAdjoint
  have hA_le_Bbar : A ≤ B.closure := by
    have := hA_le_Badj.trans hBadj_le
    rwa [hSA] at this
  have hBbar_closed : B.closure.IsClosed := hRestrictionClosable.closure_isClosed
  have h1 : A.closure ≤ B.closure := by
    have := hBbar_closed.isClosable.closure_mono hA_le_Bbar
    rwa [C206469fAux.closure_eq_self_of_isClosed _ hBbar_closed] at this
  have h2 : B.closure ≤ A.closure := hAcl.closure_mono LinearPMap.domRestrict_le
  have heq : A.closure = B.closure := le_antisymm h1 h2
  refine ⟨hAcl, ?_, heq⟩
  rw [heq]
  exact hRestrictionSelfAdjoint
