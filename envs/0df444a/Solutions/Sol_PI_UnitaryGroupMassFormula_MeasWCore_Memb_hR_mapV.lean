-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.MeasWCore.Memb.hR_mapV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:39.050488+00:00
-- url     : https://prove2.me/submissions/fdbb09bf-3744-4a7a-8b8c-e7581c4bcd34

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
theorem _root_.solution (x y : Fin n → R ⊗[F] E) :
    hR R' σ J (mapV (E := E) φ x) (mapV (E := E) φ y) = tensMap (E := E) φ (hR R σ J x y) := by
  simp only [hR, Formalism.UG.hform, map_sum, map_mul, mapV_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : tensMap (E := E) φ (sigR R σ (x i)) = sigR R' σ (tensMap (E := E) φ (x i)) := by
    have := congrArg (fun f : R ⊗[F] E →+* R' ⊗[F] E => f (x i)) (tensMap_sigR (E := E) φ σ)
    simpa using this
  rw [h1]
  simp [JR, tensMap_inclR]
end PI.UnitaryGroupMassFormula.MeasWCore.Memb
