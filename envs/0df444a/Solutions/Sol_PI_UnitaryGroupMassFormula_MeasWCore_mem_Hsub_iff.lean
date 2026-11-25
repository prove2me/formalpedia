-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.MeasWCore.mem_Hsub_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:46.141248+00:00
-- url     : https://prove2.me/submissions/3937c244-b1ab-4c46-a07e-e0dc2fc66f7f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_SplTApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_MemSpanRIffSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_mapV_ratV
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_lin_haMap
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_eq_iff_split
import Theorems.Thm_Formalism_L2_SG_Sub_mem_stabT


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
open Memb
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)
namespace PI.UnitaryGroupMassFormula.MeasWCore
theorem _root_.solution (hinj : Function.Injective (splT (F := F) (E := E))) {r : ℕ} (P : Frame E n r)
    (g : HA (AF F) σ J) :
    g ∈ Hsub (AF F) σ J P ↔ haMap σ J (fstA F) g ∈ Hsub (Ainf F) σ J P ∧
      haMap σ J (sndA F) g ∈ Hsub (Af F) σ J P := by
  unfold Hsub
  rw [mem_stabT, mem_stabT, mem_stabT]
  constructor
  · intro h
    refine ⟨fun b => ?_, fun b => ?_⟩
    · rw [← mapV_ratV (fstA F), lin_haMap, h b]
    · rw [← mapV_ratV (sndA F), lin_haMap, h b]
  · rintro ⟨h1, h2⟩ b
    rw [eq_iff_split hinj]
    constructor
    · rw [← lin_haMap, mapV_ratV]
      exact h1 b
    · rw [← lin_haMap, mapV_ratV]
      exact h2 b
end PI.UnitaryGroupMassFormula.MeasWCore
