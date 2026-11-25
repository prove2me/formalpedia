-- Prove2me | solution 1 for PI.OddDualWeyl.Intw.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:29.851215+00:00
-- url     : https://prove2.me/submissions/27479ec4-49dc-4050-aedb-fb4c8a0b9032

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_TransvectionMulApply
import Theorems.Thm_PI_OddDualWeyl_Intw_rowGen_dualM

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
theorem _root_.solution (a b : Fin k) (hab : a ≠ b) (f' : MvPolynomial (Fin k × Fin k) R) :
    rowGen R a b (dualSub R k f') =
      (Polynomial.map (dualSub R k : MvPolynomial (Fin k × Fin k) R →+* _)
        (rowGen R b a f')).comp (-Polynomial.X) := by
  refine MvPolynomial.induction_on (motive := fun g => PI.OddDualWeyl.rowGen R a b (PI.OddDualWeyl.dualSub R k g) =
      (Polynomial.map (PI.OddDualWeyl.dualSub R k : MvPolynomial (Fin k × Fin k) R →+* _)
        (PI.OddDualWeyl.rowGen R b a g)).comp (-Polynomial.X)) f' ?_ ?_ ?_
  · intro r
    simp [PI.OddDualWeyl.dualSub, PI.OddDualWeyl.rowGen]
  · intro p q hp hq
    rw [map_add, map_add, hp, hq, map_add, Polynomial.map_add, Polynomial.add_comp]
  · intro p v hp
    have hv : PI.OddDualWeyl.rowGen R a b (PI.OddDualWeyl.dualSub R k (X v)) =
        (Polynomial.map (PI.OddDualWeyl.dualSub R k : MvPolynomial (Fin k × Fin k) R →+* _)
          (PI.OddDualWeyl.rowGen R b a (X v))).comp (-Polynomial.X) := by
      obtain ⟨i, j⟩ := v
      have e1 : (PI.OddDualWeyl.dualSub R k : MvPolynomial (Fin k × Fin k) R →+* _) (X (i, j)) =
          PI.OddDualWeyl.dualM R k i j := by
        show PI.OddDualWeyl.dualSub R k (X (i, j)) = _
        simp only [PI.OddDualWeyl.dualSub, aeval_X]
      have e2 : (PI.OddDualWeyl.dualSub R k : MvPolynomial (Fin k × Fin k) R →+* _) (X (b, j)) =
          PI.OddDualWeyl.dualM R k b j := by
        show PI.OddDualWeyl.dualSub R k (X (b, j)) = _
        simp only [PI.OddDualWeyl.dualSub, aeval_X]
      have e3 : PI.OddDualWeyl.rowGen R b a (X (i, j) : MvPolynomial (Fin k × Fin k) R) =
          Polynomial.C (X (i, j)) + (if i = a then Polynomial.X * Polynomial.C (X (b, j)) else 0) := by
        simp only [PI.OddDualWeyl.rowGen, aeval_X]
      have e4 : PI.OddDualWeyl.dualSub R k (X (i, j) : MvPolynomial (Fin k × Fin k) R) =
          PI.OddDualWeyl.dualM R k i j := e1
      rw [e4, rowGen_dualM a b hab, e3]
      split_ifs with h
      · rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_X,
          Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.C_comp,
          Polynomial.X_comp, e1, e2]
        ring
      · rw [sub_zero, add_zero, Polynomial.map_C, Polynomial.C_comp, e1]
    rw [map_mul, map_mul, hp, hv, map_mul, Polynomial.map_mul, Polynomial.mul_comp]
end PI.OddDualWeyl.Intw
