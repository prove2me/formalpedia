-- Prove2me | solution 1 for SensitivityPhysicalLowPacking.internal_card
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:20:42.992648+00:00
-- url     : https://prove2.me/submissions/00ea5740-e15e-4e21-abde-4ad751c9f171

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_PhysicalLowPacking
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace Sensitivity213981Formal.TournamentHighRows
end Sensitivity213981Formal.TournamentHighRows
namespace SensitivityActiveSocketGeometry
end SensitivityActiveSocketGeometry
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityLowPacking
end SensitivityLowPacking
namespace SensitivityMarkedSocketPopulation
end SensitivityMarkedSocketPopulation
namespace SensitivityPhysicalLowPacking
end SensitivityPhysicalLowPacking
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityTournamentBudgets
end SensitivityTournamentBudgets

section


/-! Exact passage from low physical rows to the macro multiplicity packing.
The loss of an internal tournament edge costs one guard at its source, while an
external macro conflict costs every occupied physical row at its destination. -/
namespace SensitivityPhysicalLowPacking

noncomputable section
open scoped Classical BigOperators
open SensitivityLowPacking SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityActiveSocketGeometry SensitivityMarkedSocketPopulation
open Sensitivity213981Formal.TournamentHighRows SensitivityTournamentBudgets
set_option autoImplicit false

variable {M B I Color : Type} [Fintype M] [Fintype B] {L : ℕ}







theorem mem_fiber (rows : Finset (M × B)) (m : M) (b : B) : b ∈ fiber rows m ↔ (m, b) ∈ rows := by
  simp [fiber]

























end
end SensitivityPhysicalLowPacking

end

/-! Exact passage from low physical rows to the macro multiplicity packing.
The loss of an internal tournament edge costs one guard at its source, while an
external macro conflict costs every occupied physical row at its destination. -/
open SensitivityPhysicalLowPacking
open scoped Classical BigOperators
open SensitivityLowPacking SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityActiveSocketGeometry SensitivityMarkedSocketPopulation
open Sensitivity213981Formal.TournamentHighRows SensitivityTournamentBudgets
set_option autoImplicit false
variable {M B I Color : Type} [Fintype M] [Fintype B] {L : ℕ}

theorem solution (rows : Finset (M × B)) (arc : B → B → Prop) (m : M) (b : B) :
    (rows.filter fun w => w.1 = m ∧ arc b w.2).card = ((fiber rows m).filter (arc b)).card := by
  symm
  apply Finset.card_bij (fun c _ => (m, c))
  · intro c hc
    obtain ⟨hc, harc⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr ⟨(mem_fiber rows m c).mp hc, rfl, harc⟩
  · intro a _ c _ heq
    exact congrArg Prod.snd heq
  · rintro ⟨n, c⟩ hw
    obtain ⟨hw, hnm, harc⟩ := Finset.mem_filter.mp hw
    change n = m at hnm
    subst n
    exact ⟨c, Finset.mem_filter.mpr ⟨(mem_fiber rows m c).mpr hw, harc⟩, rfl⟩
