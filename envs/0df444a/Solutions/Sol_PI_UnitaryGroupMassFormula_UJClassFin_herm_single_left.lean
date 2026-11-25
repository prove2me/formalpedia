-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.herm_single_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:44:27.274841+00:00
-- url     : https://prove2.me/submissions/df9ca8f0-be9f-4d2f-84a2-82f4311587d6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_ClassFiniteOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermSingleLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.HermLatFin
variable {E : Type} [Field E] {M : ℕ} (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E)
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (i : Fin M) (k : ℕ) (y : Fin M → E) :
    herm σ J (Pi.single i (k : E)) y = (k : E) * (J.mulVec y) i := by
  classical
  simp only [herm]
  rw [Finset.sum_eq_single i]
  · simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp
end PI.UnitaryGroupMassFormula.UJClassFin
