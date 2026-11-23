-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.MeasWCore.Memb.lin_haMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:00.383654+00:00
-- url     : https://prove2.me/submissions/a8b33f6a-3d27-424d-ba1b-47fd94c0f0a3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_SplTApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_MemSpanRIffSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (g : HA R σ J) (x : Fin n → R ⊗[F] E) :
    lin R' σ J (haMap σ J φ g) (mapV (E := E) φ x) = mapV (E := E) φ (lin R σ J g x) := by
  funext i
  change Matrix.mulVec (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map
      (tensMap (E := E) φ)) (fun j => tensMap (E := E) φ (x j)) i =
    tensMap (E := E) φ (Matrix.mulVec ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (R ⊗[F] E)) x i)
  rw [RingHom.map_mulVec]
  rfl
end PI.UnitaryGroupMassFormula.MeasWCore.Memb
