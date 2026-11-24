-- Prove2me | solution 1 for PI.KLW.Ind.rp_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:45:09.444227+00:00
-- url     : https://prove2.me/submissions/7f122bcf-4baf-473a-8de6-ab0139f4814c

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] (p : ℕ) : Rp K p 1 :=
  ⟨1, Nat.coprime_one_left p, by rw [Nat.cast_one, mul_one]; exact one_mem _⟩
end PI.KLW.Ind
