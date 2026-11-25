-- Prove2me | solution 1 for Potential.exactPotential_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:06:18.4168+00:00
-- url     : https://prove2.me/submissions/8b71d3ce-e2d2-4618-9903-fb2bb5a580de

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
public import Theorems.Thm_Potential_exactPotential_pathIntegral
public import Theorems.Thm_Potential_endpoint_all_setMoves

set_option autoImplicit true
@[expose] public section
public section
open Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
namespace Potential
theorem _root_.solution [Fintype I] [∀ i, Nonempty (A i)]
    (u : Payoff A) (P Q : Profile A → ℝ)
    (hp : ExactPotential u P) (hq : ExactPotential u Q) :
    ∃ c : ℝ, ∀ s, P s = Q s + c := by
  classical
  let base : Profile A := fun i => Classical.choice (inferInstance : Nonempty (A i))
  refine ⟨P base - Q base, ?_⟩
  intro s
  let ms := Finset.univ.toList.map (fun i => (⟨i, s i⟩ : Move A))
  have he : endpoint base ms = s := endpoint_all_setMoves base s
  have hp' := exactPotential_pathIntegral u P hp base ms
  have hq' := exactPotential_pathIntegral u Q hq base ms
  rw [he] at hp' hq'
  linarith
end Potential
