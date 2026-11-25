-- Prove2me | solution 1 for PI.VolStabW.hasDens_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:26:01.269603+00:00
-- url     : https://prove2.me/submissions/a652185e-e073-453a-85d2-854a66b0d439

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVCos
import Theorems.Thm_PI_VolStabW_hasDens_zero
import Theorems.Thm_PI_VolStabW_HasDens_add

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
open MeasureTheory Topology Set Filter
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}
namespace PI.VolStabW
theorem _root_.solution [IsFiniteMeasureOnCompacts ν] {κ : Type} (φ : κ → V → ℝ) (g : κ → X → ℝ) :
    ∀ T : Finset κ, (∀ i ∈ T, HasDens μ f ι ν (φ i) (g i)) →
      HasDens μ f ι ν (fun v => ∑ i ∈ T, φ i v) (fun b => ∑ i ∈ T, g i b) := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty => intro _; simpa using (hasDens_zero (μ := μ) (f := f) (ι := ι) (ν := ν))
  | insert i T hi ih =>
    intro h
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
end PI.VolStabW
