-- Prove2me | solution 1 for PI.DatumBlockEigen.Unit.shiftJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:18:02.984996+00:00
-- url     : https://prove2.me/submissions/39cf2528-b086-4dd1-8768-fff42a4c670a

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
import Theorems.Thm_PI_DatumBlockEigen_Unit_int_mul
import Theorems.Thm_PI_DatumBlockEigen_Unit_II_int
import Theorems.Thm_PI_DatumBlockEigen_Unit_congOf

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
namespace PI.DatumBlockEigen.Unit
theorem _root_.solution (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0) (hL : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) {a : ℕ}
    {J' : Subgroup (GL (Fin a) F)} (hK : Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J')
    (hJ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a) (g : J') (y : Matrix (Fin a) (Fin a) F)
    (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ) :
    ∃ U : J', (U : GL (Fin a) F) ∈ Formalism.DoubleCosetMeasures.congSub O ϖ a ∧
      (((g * U : J') : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) =
        ((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) + y := by
  set gi : Matrix (Fin a) (Fin a) F := (((g : GL (Fin a) F)⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)
  have hgi : ∀ i j, gi i j ∈ O := (hJ (J'.inv_mem g.2)).1
  have hyI : ∀ i j, (ϖ⁻¹ • y) i j ∈ O := fun i j => by
    obtain ⟨o, ho, e⟩ := hy i j
    rw [Matrix.smul_apply, e, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]; exact ho
  have hu : ∀ i j, (1 + gi * y) i j ∈ O := fun i j => by
    rw [Matrix.add_apply]
    refine O.add_mem ?_ (int_mul hgi (II_int hϖ hy) i j)
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, O.one_mem, O.zero_mem]
  have h1 : ∀ i j, (ϖ⁻¹ • ((1 + gi * y) - 1)) i j ∈ O := by
    rw [add_sub_cancel_left, ← Matrix.mul_smul]
    exact int_mul hgi hyI
  obtain ⟨U, hU, hUe⟩ := congOf hϖ hϖ0 hL _ hu h1
  refine ⟨⟨U, hK hU⟩, hU, ?_⟩
  rw [Subgroup.coe_mul, Units.val_mul, hUe, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc]
  rw [show ((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) * gi = 1 by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one], Matrix.one_mul]
end PI.DatumBlockEigen.Unit
