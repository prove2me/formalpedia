-- Prove2me | solution 1 for P2M_MatchingLogic_Applicative_stepAt_coord__a3e4686a9bc3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:02.465204+00:00
-- url     : https://prove2.me/submissions/1a4d4a0d-75c4-4746-9610-91b5f2255d8d

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
namespace MatchingLogic.Applicative
theorem _root_.solution (M : Model (appSig Const)) (u v : M.carrier) :
    M.stepAt coord₂ u v ↔ ∃ a b : M.carrier, u ∈ M.interp appSym ![a, b] ∧ v = b := by
  change (∃ ab : Fin 2 → M.carrier, u ∈ M.interp none ab ∧ v = ab 1) ↔
    ∃ a b : M.carrier, u ∈ M.interp none ![a, b] ∧ v = b
  constructor
  · rintro ⟨ab, hab, hv⟩
    refine ⟨ab 0, ab 1, ?_, hv⟩
    rw [show ![ab 0, ab 1] = ab by
      funext i
      rcases fin_two_cases i with rfl | rfl <;> rfl]
    exact hab
  · rintro ⟨a, b, hab, hv⟩
    refine ⟨![a, b], hab, ?_⟩
    exact hv
end MatchingLogic.Applicative
