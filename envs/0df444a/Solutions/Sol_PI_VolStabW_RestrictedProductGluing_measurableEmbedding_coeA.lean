-- Prove2me | solution 1 for PI.VolStabW.RestrictedProductGluing.measurableEmbedding_coeA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:56:34.387397+00:00
-- url     : https://prove2.me/submissions/b47f1fd8-2ecb-4c68-8ba2-70aa0a04267a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoPolish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RPGlue
import Theorems.Thm_PI_VolStabW_TopoPolish_polish_of_lcsc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct RestrictedProduct
open PI.VolStabW.RestrictedProductGluing
open PositiveNearLattice
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {M a d : ℕ} (b : Module.Basis (Fin d) F E)
namespace PI.VolStabW.RestrictedProductGluing
theorem _root_.solution : MeasurableEmbedding (coeA (F := F)) := by
  have : BorelSpace (Af F) := ⟨rfl⟩
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have : PolishSpace (Af F) := TopoPolish.polish_of_lcsc (Af F)
  refine Continuous.measurableEmbedding ?_ ?_
  · exact continuous_pi fun v => by exact RestrictedProduct.continuous_eval v
  · intro x y h
    exact Subtype.ext (funext fun v => congrFun h v)
end PI.VolStabW.RestrictedProductGluing
