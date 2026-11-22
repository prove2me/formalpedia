-- Prove2me | solution 1 for P2M_MatchingLogic_Applicative_box_coord__2772cb2ce47b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:39.035806+00:00
-- url     : https://prove2.me/submissions/42c7b0da-de10-43d6-a697-04137700e63b

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Definitions.Def_LeanPool_MatchingLogic_Composite
public import Definitions.Def_LeanPool_MatchingLogic_Applicative
section
@[expose] public section
namespace MatchingLogic
namespace Applicative
variable {Const : Type} {Var : Type} [DecidableEq Var]
private theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  omega
end Applicative
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Applicative
variable {Const : Type} {Var : Type} [DecidableEq Var]
omit [DecidableEq Var]
namespace MatchingLogic.Applicative
theorem _root_.solution (ψ : Pattern (appSig Const) Var) :
    box coord₁ ψ = .imp (ap (.imp ψ .bot) Pattern.tp) .bot := by
  unfold box dia ap
  congr 2
  funext i
  change Fin 2 at i
  rcases fin_two_cases i with rfl | rfl <;> rfl
end MatchingLogic.Applicative
