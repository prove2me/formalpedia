-- Prove2me | solution 1 for PI.DatumConjInvWork.II_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:45.319057+00:00
-- url     : https://prove2.me/submissions/135f88f9-e4eb-4c2c-95d4-9ab99c4d09c6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumConjInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugationInvariance_SecondRowsBlockDiagMul
import Theorems.Thm_P2M_PI_DatumConjInvWork_II_mul__0a00f185cfa1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.DatumConjInvWork
variable {F : Type} [Field F] {a t : ℕ}
namespace PI.DatumConjInvWork
theorem _root_.solution (O : Subring F) (ϖ : F) (k : GL (Fin a) F) (hk : k ∈ Formalism.DoubleCosetMeasures.GLint O a)
    (y : Matrix (Fin t) (Fin a) F) :
    y * (k : Matrix (Fin a) (Fin a) F) ∈ Formalism.DoubleCosetMeasures.IIset O ϖ ↔ y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ := by
  have hk' : (∀ i j, (k : Matrix (Fin a) (Fin a) F) i j ∈ O) ∧
      (∀ i j, ((k⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) i j ∈ O) := hk
  constructor
  · intro h
    have h2 := II_mul' O ϖ _ h _ hk'.2
    rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h2
  · intro h
    exact II_mul' O ϖ y h _ hk'.1
end PI.DatumConjInvWork
