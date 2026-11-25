-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.MeasWCore.Memb.hR_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:42.065109+00:00
-- url     : https://prove2.me/submissions/e40f7407-0e3f-4c4a-b39b-0aec24a43ea0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_SplTApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_MemSpanRIffSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_mapV_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.MeasWCore.Memb.mapV_apply

set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.MeasWCore
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField
open scoped TensorProduct
open PI.UnitaryGroupMassFormula.MeasWCore.Memb
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R') {n : ℕ}
variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
namespace PI.UnitaryGroupMassFormula.MeasWCore.Memb
theorem _root_.solution (x : Fin n → R ⊗[F] E) : hR R σ J x 0 = 0 := by
  simp [hR, Formalism.UG.hform]
end PI.UnitaryGroupMassFormula.MeasWCore.Memb
