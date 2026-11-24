-- Prove2me | solution 1 for SensitivityRankedConstruction.separatesRows_of_indexing
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:20:50.655398+00:00
-- url     : https://prove2.me/submissions/0465f3d3-a882-489c-938b-24c8af4087aa

import Definitions.Def_Sensitivity214439_Phase0_Solutions_GateInvariants
import Definitions.Def_Sensitivity214439_Phase0_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentGuardCoverage
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! Pairwise orientation gives the guard that separates strict row colors. -/
open SensitivityRankedConstruction
open SensitivityHighHeadGuardBridge

theorem solution {V S : Type} {guards : GuardFamily V S}
    {arc : V → V → Prop} (indexing : GuardIndexing guards arc)
    (hcovers : CoversPairs arc) : SeparatesRows guards := by
  intro v w hne
  have lift (a b : V) (hab : arc a b) :
      ∃ check ∈ guards a, ∃ s, (b, s) ∈ check := by
    obtain ⟨socket, hs⟩ := indexing.nonempty a b hab
    refine ⟨indexing.check a b, indexing.member a b hab, socket.2, ?_⟩
    have heq : socket = (b, socket.2) :=
      Prod.ext (indexing.destination a b socket hs) rfl
    exact heq ▸ hs
  rcases hcovers v w hne with hvw | hwv
  · exact Or.inl (lift v w hvw)
  · exact Or.inr (lift w v hwv)
