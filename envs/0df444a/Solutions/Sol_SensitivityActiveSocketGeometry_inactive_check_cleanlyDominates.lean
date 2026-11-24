-- Prove2me | solution 1 for SensitivityActiveSocketGeometry.inactive_check_cleanlyDominates
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:34:13.337829+00:00
-- url     : https://prove2.me/submissions/a3f21b13-27a0-43e0-a161-41d5d53df017

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_ActiveSocketMacroGeometry
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
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

theorem solution
    (row : RowFamily I Color L) (macroArc : M → M → Prop)
    (label : M → M → Bool) (internalArc : B → B → Prop)
    (active : M × B → Bool) (cutoff : ℕ)
    (x : (((M × B) × Bool) × I) → Bool)
    {marker v : M × B} (harc : pairedArc macroArc internalArc marker v)
    (hactive : passes row cutoff (socketInput x (v, active v)))
    (hquiet : ¬ guardActive row cutoff x (pairedCheck label marker v)) :
    CleanlyDominates macroArc label active marker.1 v := by
  have hnot : (v, active v) ∉ pairedCheck label marker v := by
    intro hmem
    exact hquiet ⟨(v, active v), hmem, hactive⟩
  rcases harc with hext | hint
  · refine ⟨hext.2, ?_⟩
    intro heq
    apply hnot
    simp only [pairedCheck, if_neg hext.1, heq, Finset.mem_singleton]
  · exfalso
    apply hnot
    simp only [pairedCheck, if_pos hint.1]
    cases active v <;> simp
