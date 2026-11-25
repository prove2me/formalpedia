-- Prove2me | solution 1 for PI.OddDualWeyl.Intw.rowGen_dualM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:12:25.836121+00:00
-- url     : https://prove2.me/submissions/747149f5-8978-4b38-be55-ec882b7088a4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_TransvectionMulApply
import Theorems.Thm_PI_OddDualWeyl_Intw_mul_transvection_apply
import Theorems.Thm_PI_OddDualWeyl_Intw_adjugate_transvection
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
theorem _root_.solution (a b : Fin k) (hab : a ≠ b) (i j : Fin k) :
    rowGen R a b (dualM R k i j) = Polynomial.C (dualM R k i j) -
      (if i = a then Polynomial.X * Polynomial.C (dualM R k b j) else 0) := by
  have hadj : (rowGen R a b).toRingHom.mapMatrix (adjugate (genM R k)) =
      (Polynomial.C : MvPolynomial (Fin k × Fin k) R →+* _).mapMatrix (adjugate (genM R k)) *
        transvection b a (-Polynomial.X) := by
    rw [RingHom.map_adjugate, rowGen_genM, adjugate_mul_distrib,
      adjugate_transvection (Ne.symm hab), ← RingHom.map_adjugate]
  have h2 := congrFun (congrFun hadj (Fin.rev j)) i
  rw [mul_transvection_apply] at h2
  simp only [RingHom.mapMatrix_apply, map_apply] at h2
  have e1 : dualM R k i j = adjugate (genM R k) (Fin.rev j) i := rfl
  have e2 : dualM R k b j = adjugate (genM R k) (Fin.rev j) b := rfl
  rw [e1, e2]
  change (rowGen R a b).toRingHom _ = _
  rw [h2]
  split_ifs <;> ring
end PI.OddDualWeyl.Intw
