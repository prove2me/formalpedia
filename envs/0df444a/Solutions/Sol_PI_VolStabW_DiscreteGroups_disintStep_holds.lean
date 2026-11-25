-- Prove2me | solution 1 for PI.VolStabW.DiscreteGroups.disintStep_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:32.266858+00:00
-- url     : https://prove2.me/submissions/c9ea76d4-418a-4168-8a99-cfaa89403e17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibGlue
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibDis
import Theorems.Thm_PI_VolStabW_DiscreteGroups_cover
import Theorems.Thm_PI_VolStabW_DiscreteGroups_open_case
import Theorems.Thm_PI_VolStabW_DiscreteGroups_null_compl
import Theorems.Thm_PI_VolStabW_DiscreteGroups_meas_fib

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DiscreteGroups
open MeasureTheory Topology Set Filter PI.VolStabW PI.VolStabW.Glue
open scoped ENNReal
namespace PI.VolStabW.DiscreteGroups
theorem _root_.solution : DisintStep := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν hμ hν hpos f ι U hf hι hr hU fib h0 h2 h3 φ hφ
  have hmf : Measurable fib :=
    Measure.measurable_of_measurable_coe fib (meas_fib hf hι hr hU h0 h2 h3)
  have hρ : μ.restrict U = ν.bind fib := by
    obtain ⟨B, hB, hBU⟩ := cover (univ : Set V) isOpen_univ
    refine Measure.ext_of_generateFrom_of_iUnion {s : Set V | IsOpen s} B BorelSpace.measurable_eq
      isPiSystem_isOpen hBU (fun i => (hB i).1) (fun i => ?_) ?_
    · exact ((Measure.restrict_apply_le _ _).trans_lt
        ((measure_mono subset_closure).trans_lt (hB i).2.1.measure_lt_top)).ne
    · intro s hs
      rw [Measure.restrict_apply (hs : IsOpen s).measurableSet,
        Measure.bind_apply hs.measurableSet hmf.aemeasurable,
        (open_case hf hι hr hU h0 h2 h3 (s ∩ U) (hs.inter hU) inter_subset_right).2]
      congr 1
      funext b
      rw [← measure_inter_add_diff s hU.measurableSet,
        measure_mono_null (show s \ U ⊆ Uᶜ from fun x hx => hx.2)
          (null_compl hf hι hr hU h0 h2 h3 b), add_zero]
  rw [hρ, Measure.lintegral_bind hmf.aemeasurable hφ.aemeasurable]
end PI.VolStabW.DiscreteGroups
