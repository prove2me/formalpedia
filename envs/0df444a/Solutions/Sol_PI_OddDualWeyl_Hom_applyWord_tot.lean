-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.applyWord_tot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:23:27.772535+00:00
-- url     : https://prove2.me/submissions/b258d739-c9ef-4d19-a2b1-4ca9db7fa213

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
import Theorems.Thm_PI_OddDualWeyl_Hom_rowDiv_tot

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
theorem _root_.solution (wd : List (Fin k × Fin k × ℕ)) {f : MvPolynomial (Fin k × Fin k) R} {n : ℕ}
    (hf : IsHomogeneous f n) : IsHomogeneous (applyWord R wd f) n := by
  induction wd with
  | nil => exact hf
  | cons x w ih => exact rowDiv_tot x.1 x.2.1 x.2.2 ih
end PI.OddDualWeyl.Hom
