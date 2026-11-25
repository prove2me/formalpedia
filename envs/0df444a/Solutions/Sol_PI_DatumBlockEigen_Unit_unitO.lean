-- Prove2me | solution 1 for PI.DatumBlockEigen.Unit.unitO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:34:42.069656+00:00
-- url     : https://prove2.me/submissions/127b709e-feab-438a-9cde-7cd32bdaab28

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
import Theorems.Thm_PI_DatumBlockEigen_Unit_mem_pI

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
theorem _root_.solution (hϖ : ϖ ∈ O) (hL : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) (x : O)
    (hx : IsUnit (Ideal.Quotient.mk (pI O ϖ hϖ) x)) : (x : F) ≠ 0 ∧ (x : F)⁻¹ ∈ O := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (pI O ϖ hϖ)), Ideal.Quotient.eq, mem_pI] at hy
  obtain ⟨c, hc, e⟩ := hy
  have e' : (x : F) * y0 - 1 = ϖ * c := by push_cast at e; exact e
  have hz : ∀ o ∈ O, (x : F) * y0 ≠ ϖ * o := by
    intro o ho h
    apply hL.1
    have h1 : ϖ * (o - c) = 1 := by linear_combination e' - h
    rw [inv_eq_of_mul_eq_one_right h1]
    exact O.sub_mem ho hc
  have hz0 : (x : F) * y0 ≠ 0 := by simpa using hz 0 O.zero_mem
  have hzi : ((x : F) * y0)⁻¹ ∈ O := hL.2 _ (O.mul_mem x.2 y0.2) hz
  have hx0 : (x : F) ≠ 0 := left_ne_zero_of_mul hz0
  have hy0 : (y0 : F) ≠ 0 := right_ne_zero_of_mul hz0
  refine ⟨hx0, ?_⟩
  have : (x : F)⁻¹ = y0 * ((x : F) * y0)⁻¹ := by
    rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hy0, mul_one]
  rw [this]
  exact O.mul_mem y0.2 hzi
end PI.DatumBlockEigen.Unit
