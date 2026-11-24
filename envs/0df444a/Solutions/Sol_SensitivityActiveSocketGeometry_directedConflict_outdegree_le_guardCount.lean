-- Prove2me | solution 1 for SensitivityActiveSocketGeometry.directedConflict_outdegree_le_guardCount
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:34:09.502745+00:00
-- url     : https://prove2.me/submissions/341726ef-792a-4756-93e8-cbc9b618cd83

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActiveSocketMacroGeometry
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentSocketGuards
import Definitions.Def_Sensitivity214439_Phase0_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityActiveSocketGeometry
end SensitivityActiveSocketGeometry
namespace SensitivityCyclicTokens
end SensitivityCyclicTokens
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction

section


/-!
Actual selected positive sockets induce the macro conflict graph used in the
population argument. An independent set contains at most one row per macro.
The complement of each selected socket is a coherent token. Every directed
conflict pays for a different actually active guard, including internal OR
checks. Clean domination gives exactly the literal perfect-marker condition.
-/

namespace SensitivityActiveSocketGeometry

noncomputable section
open scoped Classical Fin.CommRing
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge SensitivityCyclicTokens
set_option autoImplicit false

variable {M B I Color : Type} {L n : ℕ}









































theorem directedConflict_active
    (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop)
    (active : M × B → Bool) (cutoff : ℕ)
    (x : (((M × B) × Bool) × I) → Bool)
    {v w : M × B} (h : DirectedConflict macroArc label internalArc active v w)
    (hactive : passes row cutoff (socketInput x (w, active w))) :
    guardActive row cutoff x (pairedCheck label v w) := ⟨(w, active w), h.2, hactive⟩


















end
end SensitivityActiveSocketGeometry

end

/-!
Actual selected positive sockets induce the macro conflict graph used in the
population argument. An independent set contains at most one row per macro.
The complement of each selected socket is a coherent token. Every directed
conflict pays for a different actually active guard, including internal OR
checks. Clean domination gives exactly the literal perfect-marker condition.
-/
open SensitivityActiveSocketGeometry
open scoped Classical Fin.CommRing
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge SensitivityCyclicTokens
set_option autoImplicit false
variable {M B I Color : Type} {L n : ℕ}

theorem solution [Fintype M] [Fintype B]
    (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop)
    (active : M × B → Bool) (vertices : Finset (M × B)) (cutoff : ℕ)
    (x : (((M × B) × Bool) × I) → Bool)
    (hactive : ∀ w ∈ vertices, passes row cutoff (socketInput x (w, active w)))
    (v : M × B) :
    (vertices.filter (DirectedConflict macroArc label internalArc active v)).card ≤
      guardCount row (pairedTournamentGuards macroArc label internalArc) v cutoff x := by
  let idx := pairedIndexing macroArc label internalArc
  unfold guardCount
  apply Finset.card_le_card_of_injOn (idx.check v)
  · intro w hw
    obtain ⟨hw, hdir⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨idx.member v w hdir.1,
      directedConflict_active row macroArc label internalArc active cutoff x hdir
        (hactive w hw)⟩
  · intro w hw z hz heq
    have hdir := (Finset.mem_filter.mp hw).2
    have hs : (w, active w) ∈ idx.check v w := hdir.2
    have hzs : (w, active w) ∈ idx.check v z := heq ▸ hs
    exact (idx.destination v w (w, active w) hs).symm.trans
      (idx.destination v z (w, active w) hzs)
