-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_UnimodLocStd_not_dvd_mul__02e58b10b277
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:34:57.67565+00:00
-- url     : https://prove2.me/submissions/76288c56-d108-4591-9ceb-46bd6152c8cc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_DescentStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_HNsmulNsmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
  (m : Type) [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {l : ℕ} (hl : l.Prime) {u v : ℤ} (hu : ¬ (l : ℤ) ∣ u) (hv : ¬ (l : ℤ) ∣ v) :
    ¬ (l : ℤ) ∣ u * v := by
  intro h
  rcases (Nat.prime_iff_prime_int.mp hl).dvd_or_dvd h with h1 | h1
  · exact hu h1
  · exact hv h1
end PI.UnitaryGroupMassFormula.UnimodLocStd
