-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.MeasWCore.Memb.mem_spanR_iff_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:50:26.58672+00:00
-- url     : https://prove2.me/submissions/f304e23c-cf94-4a67-99de-b5a710305d28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_SplTApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_MemSpanRIffSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_mapV_mem_spanR
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_mem_spanR_of_split

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.MeasWCore.Memb
theorem _root_.solution (hbij : Function.Bijective (splT (F := F) (E := E))) {m : ℕ}
    (Y : Fin m → Fin n → E) (s : Set (Fin m)) (w : Fin n → AF F ⊗[F] E) :
    w ∈ spanR (F := F) (AF F) Y s ↔ mapV (E := E) (fstA F) w ∈ spanR (F := F) (Ainf F) Y s ∧
      mapV (E := E) (sndA F) w ∈ spanR (F := F) (Af F) Y s :=
  ⟨fun h => ⟨mapV_mem_spanR _ Y s w h, mapV_mem_spanR _ Y s w h⟩,
    fun h => mem_spanR_of_split hbij Y s w h.1 h.2⟩
end PI.UnitaryGroupMassFormula.MeasWCore.Memb
