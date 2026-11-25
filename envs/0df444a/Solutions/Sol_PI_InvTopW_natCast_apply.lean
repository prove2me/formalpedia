-- Prove2me | solution 1 for PI.InvTopW.natCast_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:36.905424+00:00
-- url     : https://prove2.me/submissions/c08093c5-3c44-47fc-9186-4dccba342531

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_FiniteNeighbourhoodSecond

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField IsDedekindDomain Topology Filter
namespace PI.InvTopW
theorem _root_.solution (F : Type) [Field F] [NumberField F] (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (N : FiniteAdeleRing (𝓞 F) F) v = (N : v.adicCompletion F) := by
  induction N with
  | zero =>
    rw [Nat.cast_zero, Nat.cast_zero]
    rfl
  | succ n ih =>
    rw [Nat.cast_succ, Nat.cast_succ, ← ih]
    rfl
end PI.InvTopW
