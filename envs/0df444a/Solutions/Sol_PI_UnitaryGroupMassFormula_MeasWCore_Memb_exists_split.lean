-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.MeasWCore.Memb.exists_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:36.377362+00:00
-- url     : https://prove2.me/submissions/4c821f63-7db5-4ca8-8543-6d5d3f45ba53

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.MeasWCore.Memb
theorem _root_.solution (hsurj : Function.Surjective (splT (F := F) (E := E)))
    (y₁ : Fin n → Ainf F ⊗[F] E) (y₂ : Fin n → Af F ⊗[F] E) :
    ∃ v : Fin n → AF F ⊗[F] E, mapV (E := E) (fstA F) v = y₁ ∧ mapV (E := E) (sndA F) v = y₂ := by
  choose v hv using fun i => hsurj (y₁ i, y₂ i)
  refine ⟨v, funext fun i => ?_, funext fun i => ?_⟩
  · exact congrArg Prod.fst (hv i)
  · exact congrArg Prod.snd (hv i)
end PI.UnitaryGroupMassFormula.MeasWCore.Memb
