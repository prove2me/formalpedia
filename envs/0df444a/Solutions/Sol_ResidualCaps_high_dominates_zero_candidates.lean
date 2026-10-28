-- Prove2me | solution 1 for ResidualCaps.high_dominates_zero_candidates
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:42:11.22157+00:00
-- url     : https://prove2.me/submissions/2c503887-d64a-4f15-bd55-a93453179ebc

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
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_TournamentHighRows

namespace CandidateCoherence
end CandidateCoherence
namespace GuardAugmentation
end GuardAugmentation
namespace TournamentHighRows
end TournamentHighRows
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ResidualCaps
end ResidualCaps
open ResidualCaps
open scoped Classical BigOperators
open Finset TournamentHighRows CandidateCoherence GuardAugmentation
variable {V X : Type} [Fintype V] [DecidableEq V]

/-- A zero-budget target row cannot point to any high row. Thus every high
    row dominates the zero-budget negative target set. -/
theorem solution (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (children : V → Bool → X)
    (A H : Finset V) (hdis : Disjoint A H)
    (hhigh : ∀ w ∈ H, ∀ c : Bool, guard (children w c))
    (hzero : ∀ v ∈ A, (guardFailures R ell guard children v).card = 0) :
    ∀ v ∈ H, ∀ w ∈ A, R v w := by
  intro v hv w hw
  have hne : v ≠ w := by
    intro he
    subst w
    exact Finset.disjoint_left.mp hdis hw hv
  apply (hR.orient v w hne).mpr
  intro hwv
  have hmem : v ∈ guardFailures R ell guard children w :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwv,hhigh v hv (ell w v)⟩
  have hpos := Finset.card_pos.mpr ⟨v,hmem⟩
  rw [hzero w hw] at hpos
  omega
end
