-- Prove2me | solution 1 for PI.DatumBlockEigen.Unit.isUnit_det_liftO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:28:27.517381+00:00
-- url     : https://prove2.me/submissions/8c4e80b2-5c64-4fce-a3ad-e23a3001ac94

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
import Theorems.Thm_PI_DatumBlockEigen_Unit_map_liftO

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
open PI PI.DatumBlockEigen PI.DatumBlockEigen.Unit
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)
variable {O ϖ}
variable (O)
namespace PI.DatumBlockEigen.Unit
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n F)
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) (hAB : A * B = 1) :
    IsUnit (liftO O A hA).det := by
  have e : liftO O A hA * liftO O B hB = 1 := by
    have h : (liftO O A hA * liftO O B hB).map O.subtype = (1 : Matrix n n O).map O.subtype := by
      rw [Matrix.map_mul, map_liftO, map_liftO, hAB]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    exact Matrix.map_injective Subtype.val_injective h
  exact isUnit_iff_exists_inv.mpr ⟨(liftO O B hB).det, by rw [← det_mul, e, det_one]⟩
end PI.DatumBlockEigen.Unit
