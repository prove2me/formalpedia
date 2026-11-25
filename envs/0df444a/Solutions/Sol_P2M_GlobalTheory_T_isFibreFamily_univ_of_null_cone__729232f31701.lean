-- Prove2me | solution 1 for P2M_GlobalTheory_T_isFibreFamily_univ_of_null_cone__729232f31701
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:33:50.180799+00:00
-- url     : https://prove2.me/submissions/22f2b104-78e5-4be1-a720-51a325eac090

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFibreFamilyUnivOfNullCone
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFibreFamilyUnivOfNullConeStatement
import Theorems.Thm_GlobalTheory_isFibreFamily_univ_of_null_cone


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K V : Type) [NormedField K] [IsUltrametricDist K] [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (ν : Measure K) (q : V → K), Continuous q → μ {x | q x = 0} = 0 → ∀ (U : Set V) (B : Set K) (fib : K → Measure V), {x | q x ≠ 0} ⊆ U → {t | t ≠ 0} ⊆ B → IsFibreFamily μ q id U ν B fib → IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib := by
  first | exact @GlobalTheory.isFibreFamily_univ_of_null_cone | exact GlobalTheory.isFibreFamily_univ_of_null_cone | (intros; apply GlobalTheory.isFibreFamily_univ_of_null_cone <;> assumption)
end _root_.GlobalTheory.T
