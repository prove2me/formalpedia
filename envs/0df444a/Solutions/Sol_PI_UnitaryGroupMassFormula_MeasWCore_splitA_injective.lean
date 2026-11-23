-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.MeasWCore.splitA_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:00.623101+00:00
-- url     : https://prove2.me/submissions/feb01ad9-55c9-4740-bd5b-d059d52ee168

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
open Memb
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)
namespace PI.UnitaryGroupMassFormula.MeasWCore
theorem _root_.solution (hinj : Function.Injective (splT (F := F) (E := E))) :
    Function.Injective (splitA σ J) := by
  intro g g' h
  have h1 : haMap σ J (fstA F) g = haMap σ J (fstA F) g' := congrArg Prod.fst h
  have h2 : haMap σ J (sndA F) g = haMap σ J (sndA F) g' := congrArg Prod.snd h
  have hm : HA.mat (AF F) σ J g = HA.mat (AF F) σ J g' := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    apply hinj
    rw [splT_apply, splT_apply]
    refine Prod.ext ?_ ?_
    · exact congrArg (fun k => ((HA.mat (Ainf F) σ J k : GL (Fin n) (Ainf F ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j) h1
    · exact congrArg (fun k => ((HA.mat (Af F) σ J k : GL (Fin n) (Af F ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) h2
  exact Subtype.ext hm
end PI.UnitaryGroupMassFormula.MeasWCore
