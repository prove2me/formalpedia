-- Prove2me | solution 1 for TroppMatrixConcentration.ch8_log_operator_concave
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:44:31.635362+00:00
-- url     : https://prove2.me/submissions/8a5b21ed-5bee-4f50-8ff9-c3689c033ef5

import Definitions.Def_TroppMatrixConcentration_ch8_entropy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open TroppMatrixConcentration
set_option autoImplicit false

theorem solution :
    ch8_operatorConvexOn (Set.Ioi 0) (fun x => -Real.log x) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro d hd A H hA hH hAsp hHsp t ht₀ ht₁
  have hAp : IsStrictlyPositive A :=
    CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mpr
      ⟨hA, hAsp⟩
  have hHp : IsStrictlyPositive H :=
    CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mpr
      ⟨hH, hHsp⟩
  have hc := CFC.concaveOn_log.2 hAp hHp ht₀ (sub_nonneg.mpr ht₁)
    (show t + (1 - t) = 1 by ring)
  change cfc (fun x => -Real.log x) (t • A + (1 - t) • H) ≤
    t • cfc (fun x => -Real.log x) A + (1 - t) • cfc (fun x => -Real.log x) H
  simp only [cfc_neg, smul_neg, ← neg_add]
  exact neg_le_neg hc
