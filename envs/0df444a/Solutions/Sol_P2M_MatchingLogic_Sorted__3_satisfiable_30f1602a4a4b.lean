-- Prove2me | solution 1 for P2M_MatchingLogic_Sorted__3_satisfiable_30f1602a4a4b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:46:00.115644+00:00
-- url     : https://prove2.me/submissions/14620cbb-a6e2-4184-9584-a83a6488cb9e

module
public import Aesop.BuiltinRules
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Sorted

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Sorted
variable {S : MSignature} {Var : Type}
namespace MatchingLogic.Sorted
theorem _root_.solution (x y : Var) :
    ∃ M : MModel S3, M.SatSet (Γ3 (Var := Var) x y) := by
  classical
  refine ⟨singletonM3, ?_⟩
  intro γ hγ
  simp only [Γ3, Set.mem_singleton_iff] at hγ
  subst γ
  intro ρ
  ext u
  simp [MModel.app, mdenote]
end MatchingLogic.Sorted
