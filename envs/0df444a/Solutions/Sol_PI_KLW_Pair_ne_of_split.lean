-- Prove2me | solution 1 for PI.KLW.Pair.ne_of_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:44:40.537292+00:00
-- url     : https://prove2.me/submissions/9874a907-2f0e-4244-b2c8-22c0a08043db

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairOfEps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.Pair
open PI.KLW
namespace PI.KLW.Pair
theorem _root_.solution {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ}
    (hs : SplitK c p) : ∃ z, c z ≠ z := by
  obtain ⟨P, _, _, a, b, hab, ha, hb⟩ := hs
  refine ⟨(a : K), ?_⟩
  rw [hab]
  intro h
  exact hb (by rwa [RingOfIntegers.ext h])
end PI.KLW.Pair
