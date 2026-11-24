-- Prove2me | solution 1 for PI.KLW.NO.ne_of_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:46:12.718851+00:00
-- url     : https://prove2.me/submissions/f734e01b-21d3-432d-81db-6f10c7bb7005

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA

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
open PI PI.KLW PI.KLW.NO
namespace PI.KLW.NO
theorem _root_.solution {K : Type} [Field K] [NumberField K] (c : K →+* K) {p : ℕ} (h : SplitK c p) :
    ∃ z, c z ≠ z := by
  obtain ⟨P, _, _, a, b, hab, _, hb⟩ := h
  refine ⟨(a : K), fun h' => hb ?_⟩
  have : a = b := RingOfIntegers.ext (h'.symm.trans hab)
  rw [← this]; assumption
end PI.KLW.NO
