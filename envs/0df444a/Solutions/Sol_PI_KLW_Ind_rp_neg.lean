-- Prove2me | solution 1 for PI.KLW.Ind.rp_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:45:05.895469+00:00
-- url     : https://prove2.me/submissions/b11afae3-027d-4bc7-8e0f-db0a9abce85a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic

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
open PI PI.KLW PI.KLW.Ind
open PI.KLW
namespace PI.KLW.Ind
theorem _root_.solution {K : Type} [Field K] [NumberField K] {p : ℕ} {x : K} (hx : Rp K p x) :
    Rp K p (-x) := by
  obtain ⟨s, hs, hsx⟩ := hx
  exact ⟨s, hs, by rw [mul_neg]; exact neg_mem hsx⟩
end PI.KLW.Ind
