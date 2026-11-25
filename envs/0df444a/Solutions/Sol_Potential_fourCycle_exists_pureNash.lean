-- Prove2me | solution 1 for Potential.fourCycle_exists_pureNash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:04:53.0741+00:00
-- url     : https://prove2.me/submissions/b5bf3014-331a-4964-9425-3fae612094b1

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max
public import Definitions.Def_MondererShapley_Solution
public import Theorems.Thm_Potential_fourCycle_exists_exactPotential
public import Theorems.Thm_Potential_exactPotential_maximizer_pureNash

set_option autoImplicit true
@[expose] public section
public section
open Potential
variable {I : Type*} {A : I → Type*} [Fintype I] [DecidableEq I]
  [∀ i, Nonempty (A i)]
namespace Potential
theorem _root_.solution [∀ i, Fintype (A i)] (u : Payoff A)
    (hu : FourCycle u) : ∃ s : Profile A, PureNash u s := by
  classical
  obtain ⟨P, hp⟩ := fourCycle_exists_exactPotential u hu
  obtain ⟨s, _, hs⟩ := Finset.univ.exists_max_image P Finset.univ_nonempty
  exact ⟨s, exactPotential_maximizer_pureNash u P hp s
    (fun t => hs t (Finset.mem_univ t))⟩
end Potential
