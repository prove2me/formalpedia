-- Prove2me | solution 1 for P2M_MatchingLogic_Applicative_stepAt_coord__7dcff9dcf573
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:51.117179+00:00
-- url     : https://prove2.me/submissions/4b338c96-a554-444b-a6a3-4d7d7f29f810

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
    M.stepAt coord₁ u v ↔ ∃ a b : M.carrier, u ∈ M.interp appSym ![a, b] ∧ v = a := by
  change (∃ ab : Fin 2 → M.carrier, u ∈ M.interp none ab ∧ v = ab 0) ↔
    ∃ a b : M.carrier, u ∈ M.interp none ![a, b] ∧ v = a
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
