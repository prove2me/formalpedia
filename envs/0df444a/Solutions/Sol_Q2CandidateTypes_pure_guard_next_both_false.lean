-- Prove2me | solution 1 for Q2CandidateTypes.pure_guard_next_both_false
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:40:14.855444+00:00
-- url     : https://prove2.me/submissions/4e00ae03-a5cd-4abf-8ec2-89c1aaba89be

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_TournamentHighRows

namespace TournamentHighRows
end TournamentHighRows
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Q2CandidateTypes
end Q2CandidateTypes
open Q2CandidateTypes
open scoped Classical
open TournamentHighRows
variable {X V : Type}

/-- A pure lower guard candidate has two false next targets. If exactly one
    next target were false it would be the overlap type, and if neither were
    false the row would already accept. -/
theorem solution (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d b : ℕ) (x y : X) (hbQ : b+1 ≤ Q)
    (hgt : ∀ c, c ≤ Q → ∀ z, target c z → guard z)
    (hg : GuardCandidate target Q d b x y)
    (hp : ¬ PositiveCandidate guard target Q d (b+1) x y)
    (hno : ¬ Accepted target Q d x y) :
    ¬ target (b+1) x ∧ ¬ target (b+1) y := by
  classical
  have hd : d = b+1 := hg.2.1
  have hxg : guard x := hgt b hg.1 x hg.2.2.1
  have hyg : guard y := hgt b hg.1 y hg.2.2.2
  have hnotboth : ¬ (target (b+1) x ∧ target (b+1) y) := by
    rintro ⟨hx,hy⟩
    exact hno ⟨by omega,hd.symm ▸ hx,hd.symm ▸ hy⟩
  constructor
  · intro hx
    have hy : ¬ target (b+1) y := fun hy => hnotboth ⟨hx,hy⟩
    exact hp ⟨⟨hbQ,hd,Or.inr ⟨hx,hy⟩⟩,hxg,hyg⟩
  · intro hy
    have hx : ¬ target (b+1) x := fun hx => hnotboth ⟨hx,hy⟩
    exact hp ⟨⟨hbQ,hd,Or.inl ⟨hx,hy⟩⟩,hxg,hyg⟩
end
