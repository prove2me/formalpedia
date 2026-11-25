-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.generating_function_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:38.425029+00:00
-- url     : https://prove2.me/submissions/9eb2a6a8-442d-402b-bb44-4e06909d3142

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_GfPolyA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_GfPoly
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_cmul
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_det
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_det_star
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_herm
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_herm_star
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_mono
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_mul
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_PolynomialDegreeClosure_pd_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PolynomialDegreeClosure
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution : GfPoly := by
  intro k r z z'
  have hD : ∀ l : Fin (r + 2), IsPolyDeg l.val (fun g : B.Mat k r => Dmin k r z z' g l) := fun l =>
    pd_det l.val (fun g => (Zhat k r z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
      (Fin.castLE (Nat.le_of_lt_succ l.isLt))) fun i j =>
      pd_herm (Hpk k r) (fvec k r z' (Fin.castLE (Nat.le_of_lt_succ l.isLt) j))
        (fvec k r z (Fin.castLE (Nat.le_of_lt_succ l.isLt) i))
  have hDs : ∀ l : Fin (r + 2), IsPolyDeg l.val (fun g : B.Mat k r => star (Dmin k r z z' g l)) := fun l =>
    pd_det_star l.val (fun g => (Zhat k r z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
      (Fin.castLE (Nat.le_of_lt_succ l.isLt))) fun i j =>
      pd_herm_star (Hpk k r) (fvec k r z' (Fin.castLE (Nat.le_of_lt_succ l.isLt) j))
        (fvec k r z (Fin.castLE (Nat.le_of_lt_succ l.isLt) i))
  have e : (fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) = fun g =>
      Dmin k r z z' g (Fin.last (r + 1)) * star (Dmin k r z z' g (Fin.last (r + 1))) -
      ((Tz k r z * Tz k r z' : ℝ) : ℂ) *
        (Dmin k r z z' g ⟨r, by omega⟩ * star (Dmin k r z z' g ⟨r, by omega⟩)) := by
    funext g
    simp only [Gf]
    push_cast
    rw [← Complex.mul_conj, ← Complex.mul_conj]
    rfl
  rw [e]
  refine pd_sub (pd_mono ?_ (pd_mul (hD _) (hDs _))) (pd_mono ?_ (pd_cmul _ (pd_mul (hD _) (hDs _))))
  · omega
  · omega
end PI.UnitaryCorollaryDerivatives
