-- Prove2me | solution 1 for PI.TwNormLat.W.comb_zab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:31:25.856507+00:00
-- url     : https://prove2.me/submissions/fcfc99b7-97e2-4330-a73b-ed335aa89288

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_CombinationEquivInvMemUnipotentFlagGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwNormLat PI.TwNormLat.W
variable {K : Type} [Field K] {n : ℕ}
namespace PI.TwNormLat.W
theorem _root_.solution {b : Fin n → Fin n → K} (hb : UT b) (w : Fin n → K) (k0 : ℕ) (hw : Zab k0 w) :
    Zab k0 (∑ i, w i • b i) := by
  intro l hl
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : k0 ≤ i.1
  · rw [hw i hi, zero_mul]
  · have hil : i < l := Fin.lt_def.2 (by omega)
    rw [hb i l hil, mul_zero]
end PI.TwNormLat.W
