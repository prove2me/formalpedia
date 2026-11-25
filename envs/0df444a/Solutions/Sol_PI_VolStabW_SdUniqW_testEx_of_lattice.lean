-- Prove2me | solution 1 for PI.VolStabW.SdUniqW.testEx_of_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:58:22.742199+00:00
-- url     : https://prove2.me/submissions/81ff3205-c2a2-47f5-9250-500283884033

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Theorems.Thm_PI_VolStabW_SdUniqW_transform_indicator

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
open PI.VolStabW.SdUniqW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
  (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)
include hχ
namespace PI.VolStabW.SdUniqW
theorem _root_.solution (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V))
    (hA : IsClosed (ann χ L)) (K : Set V) (hK : IsCompact K) (hAK : ann χ L ⊆ K) :
    TestEx μ χ := by
  classical
  refine ⟨(L : Set V).indicator (fun _ => (1 : ℂ)),
    IsClopen.continuous_indicator ⟨L.isClosed_of_isOpen hLo, hLo⟩ continuous_const,
    HasCompactSupport.intro hLc (fun x hx => by simp [hx]), ?_, ⟨0, by simp⟩⟩
  have hfun : (fun y => ∫ x, (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y ∂μ) =
      (ann χ L).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ)) :=
    funext fun y => transform_indicator μ χ hχ L hLo y
  rw [hfun]
  exact (integrable_indicator_iff hA.measurableSet).2
    (continuousOn_const.integrableOn_compact (hK.of_isClosed_subset hA hAK))
end PI.VolStabW.SdUniqW
