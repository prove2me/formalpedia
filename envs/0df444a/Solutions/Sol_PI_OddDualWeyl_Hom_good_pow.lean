-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.good_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:58:29.050339+00:00
-- url     : https://prove2.me/submissions/3ac85537-4303-4823-b5e8-6f921b5b14cc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
import Theorems.Thm_PI_OddDualWeyl_Hom_good_congr
import Theorems.Thm_PI_OddDualWeyl_Hom_good_one
import Theorems.Thm_PI_OddDualWeyl_Hom_good_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Hom
variable {R : Type} [CommRing R] {k : ℕ}
variable {wt : Fin k × Fin k → ℤ} {δ : ℤ}
namespace PI.OddDualWeyl.Hom
theorem _root_.solution {d : ℤ} {p : Polynomial (MvPolynomial (Fin k × Fin k) R)} (hp : Good wt δ d p)
    (m : ℕ) : Good wt δ (m * d) (p ^ m) := by
  induction m with
  | zero => simpa using (good_one (R := R) (wt := wt) (δ := δ))
  | succ m ih =>
    rw [pow_succ]
    exact good_congr (by push_cast; ring) (good_mul ih hp)
end PI.OddDualWeyl.Hom
