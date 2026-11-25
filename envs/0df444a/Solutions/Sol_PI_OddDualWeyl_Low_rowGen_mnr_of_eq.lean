-- Prove2me | solution 1 for PI.OddDualWeyl.Low.rowGen_mnr_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:19:32.063887+00:00
-- url     : https://prove2.me/submissions/22c4480c-97e8-43d9-907e-06755768b5ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Theorems.Thm_PI_OddDualWeyl_Low_rowGen_mnr_mat
import Theorems.Thm_PI_OddDualWeyl_Low_C_mnr

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
open PI PI.OddDualWeyl PI.OddDualWeyl.Low
variable {R : Type*} [CommRing R]
namespace PI.OddDualWeyl.Low
theorem _root_.solution {k n : ℕ} (h : n ≤ k) (a b : Fin k) (ρ : Fin n → Fin k)
    (hρ : Function.Injective ρ) (p0 : Fin n) (hp0 : ρ p0 = b) :
    rowGen R a b (mnr R h ρ) = Polynomial.C (mnr R h ρ) +
      Polynomial.X * Polynomial.C (mnr R h (Function.update ρ p0 a)) := by
  classical
  set A : Matrix (Fin n) (Fin n) (Polynomial (MvPolynomial (Fin k × Fin k) R)) :=
    Matrix.of fun p q => Polynomial.C (X (ρ p, Fin.castLE h q)) with hA
  set v : Fin n → Polynomial (MvPolynomial (Fin k × Fin k) R) :=
    fun q => Polynomial.C (X (a, Fin.castLE h q)) with hv
  have h1 : (Matrix.of fun p q : Fin n =>
      Polynomial.C (X (ρ p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R) +
      (if ρ p = b then Polynomial.X * Polynomial.C (X (a, Fin.castLE h q)) else 0)) =
      updateRow A p0 (A p0 + (Polynomial.X : Polynomial (MvPolynomial (Fin k × Fin k) R)) • v) := by
    ext p q
    by_cases hp : p = p0
    · subst hp; simp [hA, hv, hp0]
    · have : ρ p ≠ b := fun e => hp (hρ (e.trans hp0.symm))
      simp [hA, updateRow_ne hp, this]
  have h2 : updateRow A p0 v = Matrix.of fun p q : Fin n =>
      Polynomial.C (X (Function.update ρ p0 a p, Fin.castLE h q) : MvPolynomial (Fin k × Fin k) R) := by
    ext p q
    by_cases hp : p = p0
    · subst hp; simp [hv]
    · simp [hA, updateRow_ne hp, Function.update_of_ne hp]
  rw [rowGen_mnr_mat, h1, det_updateRow_add, updateRow_eq_self, det_updateRow_smul, h2, C_mnr, C_mnr]
end PI.OddDualWeyl.Low
