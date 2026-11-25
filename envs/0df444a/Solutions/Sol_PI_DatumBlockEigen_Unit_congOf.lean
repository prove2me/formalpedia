-- Prove2me | solution 1 for PI.DatumBlockEigen.Unit.congOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:43:10.646439+00:00
-- url     : https://prove2.me/submissions/5290095d-8f76-46b5-bf9a-11ac4fdb05f0

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
import Theorems.Thm_PI_DatumBlockEigen_Unit_mem_pI
import Theorems.Thm_PI_DatumBlockEigen_Unit_isInt_inv_of_unit

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
    (u : Matrix (Fin a) (Fin a) F) (hu : ∀ i j, u i j ∈ O)
    (h1 : ∀ i j, (ϖ⁻¹ • (u - 1)) i j ∈ O) :
    ∃ U ∈ Formalism.DoubleCosetMeasures.congSub O ϖ a, (U : Matrix (Fin a) (Fin a) F) = u := by
  have hm : (Ideal.Quotient.mk (pI O ϖ hϖ)).mapMatrix (liftO O u hu) = 1 := by
    ext i j
    rw [← map_one (Ideal.Quotient.mk (pI O ϖ hϖ)).mapMatrix, RingHom.mapMatrix_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq, mem_pI]
    refine ⟨(ϖ⁻¹ • (u - 1)) i j, h1 i j, ?_⟩
    have e1 : (((1 : Matrix (Fin a) (Fin a) O) i j : O) : F) = (1 : Matrix (Fin a) (Fin a) F) i j := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [AddSubgroupClass.coe_sub, e1, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hϖ0, one_mul]
    rfl
  have hu1 : IsUnit (Ideal.Quotient.mk (pI O ϖ hϖ) (liftO O u hu).det) := by
    rw [RingHom.map_det, hm, det_one]; exact isUnit_one
  obtain ⟨hd, hinv⟩ := isInt_inv_of_unit hϖ hL u hu hu1
  exact ⟨Matrix.nonsingInvUnit u (isUnit_iff_ne_zero.mpr hd), ⟨⟨hu, hinv⟩, h1⟩, rfl⟩
end PI.DatumBlockEigen.Unit
