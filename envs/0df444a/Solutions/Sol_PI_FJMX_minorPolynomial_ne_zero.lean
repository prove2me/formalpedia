-- Prove2me | solution 1 for PI.FJMX.minorPolynomial_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:14:26.853615+00:00
-- url     : https://prove2.me/submissions/5b4cbca7-f2ae-457d-924a-4f5ca2003b00

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.FJMX
variable {R : Type*} [CommRing R] {σ : Type*}
namespace PI.FJMX
theorem _root_.solution [IsDomain R] {k : ℕ} (g : Fin k → Fin k → σ)
    (hg : Function.Injective (fun x : Fin k × Fin k => g x.1 x.2)) : minorPolynomial R g ≠ 0 := by
  have e : minorPolynomial R g = rename (fun x : Fin k × Fin k => g x.1 x.2)
      (Matrix.mvPolynomialX (Fin k) (Fin k) R).det := by
    rw [AlgHom.map_det, minorPolynomial]
    congr 1
    ext i j
    simp [Matrix.mvPolynomialX]
  rw [e]
  intro h
  apply Matrix.det_mvPolynomialX_ne_zero (m := Fin k) (R := R)
  exact (rename_injective _ hg) (by rw [h, map_zero])
end PI.FJMX
