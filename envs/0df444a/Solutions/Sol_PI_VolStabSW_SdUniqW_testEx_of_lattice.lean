-- Prove2me | solution 1 for PI.VolStabSW.SdUniqW.testEx_of_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:51:14.983959+00:00
-- url     : https://prove2.me/submissions/7114221c-7b45-4f0d-a1cf-b72b5e74abfa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Theorems.Thm_PI_VolStabSW_SdUniqW_transform_indicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.SdUniqW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
  (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)
include hχ
namespace PI.VolStabSW.SdUniqW
theorem _root_.solution (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V))
    (hA : IsClosed (ann χ L)) (K : Set V) (hK : IsCompact K) (hAK : ann χ L ⊆ K) :
    TestEx μ χ := by
  refine ⟨(L : Set V).indicator (fun _ => (1 : ℂ)), ?_, ?_, ?_, 0, ?_⟩
  · exact IsClopen.continuous_indicator ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩ continuous_const
  · exact HasCompactSupport.intro hLc fun x hx => by simp [Set.indicator, hx]
  · have e := funext (transform_indicator μ χ hχ L hLo)
    rw [e]
    have hcomp : IsCompact (ann χ L) := hK.of_isClosed_subset hA hAK
    exact (integrable_indicator_iff hA.measurableSet).2 (continuousOn_const.integrableOn_compact hcomp)
  · simp [Set.indicator]
end PI.VolStabSW.SdUniqW
