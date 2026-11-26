-- Prove2me | solution 1 for SemigroupBetti.GenData.mono_sub_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:11:28.831894+00:00
-- url     : https://prove2.me/submissions/2aa2a966-568d-4fd1-b155-5716a301ebc8

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
public import Theorems.Thm_SemigroupBetti_GenData_rep_mk
public import Theorems.Thm_SemigroupBetti_GenData_sub_mem_of_reachable
public import Theorems.Thm_SemigroupBetti_GenData_rep_sub_rep_mem
public import Theorems.Thm_SemigroupBetti_GenData_le_H_of_contributes
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_SharesVar_symm
attribute [local simp] SemigroupBetti.GenData.mem_fiber



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]
namespace SemigroupBetti.GenData
theorem _root_.solution (d : ℕ) : ∀ z z' : Fin 4 → ℕ, G.nu z = d → G.nu z' = d →
    mono K z - mono K z' ∈ Ideal.span (G.binomGens K : Set _) := by
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro z z' hz hz'
  obtain ⟨x, hx⟩ : ∃ x : G.fiber d, x.1 = z := ⟨⟨z, G.mem_fiber.2 hz⟩, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : G.fiber d, y.1 = z' := ⟨⟨z', G.mem_fiber.2 hz'⟩, rfl⟩
  subst hx hy
  by_cases hr : (G.nabla d).Reachable x y
  · exact G.sub_mem_of_reachable K IH hr
  · set Cx := (G.nabla d).connectedComponentMk x
    set Cy := (G.nabla d).connectedComponentMk y
    have hne : Cx ≠ Cy := fun h => hr (SimpleGraph.ConnectedComponent.exact h)
    have hd : d ≤ G.H := G.le_H_of_contributes (by
      unfold contributes ncomp
      exact Fintype.one_lt_card_iff.2 ⟨Cx, Cy, hne⟩)
    have h1 : mono K x.1 - mono K (G.rep Cx) ∈ Ideal.span (G.binomGens K : Set _) :=
      G.sub_mem_of_reachable K IH (x := x) (y := ⟨G.rep Cx, (Quot.out Cx).2⟩)
        (SimpleGraph.ConnectedComponent.exact (G.rep_mk Cx).symm)
    have h2 : mono K (G.rep Cy) - mono K y.1 ∈ Ideal.span (G.binomGens K : Set _) :=
      G.sub_mem_of_reachable K IH (x := ⟨G.rep Cy, (Quot.out Cy).2⟩) (y := y)
        (SimpleGraph.ConnectedComponent.exact (G.rep_mk Cy))
    have h3 := G.rep_sub_rep_mem K hd Cx Cy
    have : mono K x.1 - mono K y.1 = (mono K x.1 - mono K (G.rep Cx)) +
        (mono K (G.rep Cx) - mono K (G.rep Cy)) + (mono K (G.rep Cy) - mono K y.1) := by ring
    rw [this]
    exact add_mem (add_mem h1 h3) h2
end SemigroupBetti.GenData
