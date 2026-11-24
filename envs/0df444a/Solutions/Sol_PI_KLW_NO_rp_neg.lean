-- Prove2me | solution 1 for PI.KLW.NO.rp_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:47:19.649937+00:00
-- url     : https://prove2.me/submissions/ae328711-5e40-42e5-a4c0-7b3ebd1ef176

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
variable {K : Type} [Field K] [NumberField K] {p : ℕ}
namespace PI.KLW.NO
theorem _root_.solution {x : K} (hx : Rp K p x) : Rp K p (-x) := by
  obtain ⟨s, hs, hsx⟩ := hx
  exact ⟨s, hs, by rw [mul_neg]; exact Subring.neg_mem _ hsx⟩
end PI.KLW.NO
