-- Prove2me | solution 1 for PI.KLW.NO.rp_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:07:28.306395+00:00
-- url     : https://prove2.me/submissions/963ea92b-4bc1-4312-8fe2-9ea693066ce3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Theorems.Thm_PI_KLW_NO_rp_add
import Theorems.Thm_PI_KLW_NO_rp_neg

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
theorem _root_.solution {x y : K} (hx : Rp K p x) (hy : Rp K p y) : Rp K p (x - y) := by
  rw [sub_eq_add_neg]; exact rp_add hx (rp_neg hy)
end PI.KLW.NO
