-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.MeasWCore.Memb.eq_iff_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:00.355057+00:00
-- url     : https://prove2.me/submissions/e77da5e0-897e-4c2b-bb63-5bc3cecf5dec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_SplTApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_MemSpanRIffSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_mapV_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_splT_apply

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.MeasWCore.Memb
theorem _root_.solution (hinj : Function.Injective (splT (F := F) (E := E)))
    (w u : Fin n → AF F ⊗[F] E) :
    w = u ↔ mapV (E := E) (fstA F) w = mapV (E := E) (fstA F) u ∧
      mapV (E := E) (sndA F) w = mapV (E := E) (sndA F) u := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    funext i
    apply hinj
    rw [splT_apply, splT_apply]
    exact Prod.ext (congrFun h1 i) (congrFun h2 i)
end PI.UnitaryGroupMassFormula.MeasWCore.Memb
