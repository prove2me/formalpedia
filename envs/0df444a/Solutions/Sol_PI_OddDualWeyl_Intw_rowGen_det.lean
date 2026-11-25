-- Prove2me | solution 1 for PI.OddDualWeyl.Intw.rowGen_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:12:22.789287+00:00
-- url     : https://prove2.me/submissions/ea7337e1-0a93-42f0-8840-ff44f0b7eec6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_TransvectionMulApply
import Theorems.Thm_PI_OddDualWeyl_Intw_rowGen_genM

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
open PI.OddDualWeyl.Intw
variable {R : Type} [CommRing R] {k : ℕ}
namespace PI.OddDualWeyl.Intw
theorem _root_.solution (a b : Fin k) (hab : a ≠ b) :
    rowGen R a b (genM R k).det = Polynomial.C (genM R k).det := by
  calc PI.OddDualWeyl.rowGen R a b (PI.OddDualWeyl.genM R k).det
      = ((PI.OddDualWeyl.rowGen R a b).toRingHom.mapMatrix (PI.OddDualWeyl.genM R k)).det :=
        RingHom.map_det (PI.OddDualWeyl.rowGen R a b).toRingHom (PI.OddDualWeyl.genM R k)
    _ = Polynomial.C (PI.OddDualWeyl.genM R k).det := by
        rw [rowGen_genM, det_mul, det_transvection_of_ne b a hab.symm, one_mul,
          ← RingHom.map_det]
end PI.OddDualWeyl.Intw
