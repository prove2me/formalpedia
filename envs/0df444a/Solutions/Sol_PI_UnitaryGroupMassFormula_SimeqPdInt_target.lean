-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.SimeqPdInt.target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:46.11927+00:00
-- url     : https://prove2.me/submissions/b07c1ca4-86bd-4d75-b471-a243d45024b2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SimeqPdInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialCoefficientSeries_CoeffExpMvEqTs
import Theorems.Thm_PI_UnitaryGroupMassFormula_SimeqPdInt_pd_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_SimeqPdInt_pderiv_expMv
import Theorems.Thm_PI_UnitaryGroupMassFormula_SimeqPdInt_int_pderiv
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_expMv_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_expMv_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_int_expMv_neg
import Theorems.Thm_PI_UnitaryGroupMassFormula_CubeRelationOfParallelogram_int_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.SimeqPdInt
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.UnitaryGroupMassFormula.SimeqPdInt
theorem _root_.solution : PI.SimeqPdInt.Target := by
  intro p _ σ _ f hf k
  obtain ⟨h0, hE⟩ := hf
  rw [sub_zero] at h0 hE
  have hE' : PI.FglGram.IntegralMv (PI.FglGram.expMv f) := hE
  have hinv := PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.int_expMv_neg h0 hE'
  have hWV : PI.FglGram.expMv (-f) * PI.FglGram.expMv f = 1 := by
    rw [← PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.expMv_add (by rw [map_neg, h0, neg_zero]) h0, neg_add_cancel,
      PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.expMv_zero]
  have key : PI.SimeqPdInt.pd k f =
      PI.FglGram.expMv (-f) * pderiv ℂ_[p] k (PI.FglGram.expMv f) := by
    rw [pd_eq, pderiv_expMv k h0, ← mul_assoc, hWV, one_mul]
  rw [key]
  exact PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.int_mul hinv (int_pderiv k hE')
end PI.UnitaryGroupMassFormula.SimeqPdInt
