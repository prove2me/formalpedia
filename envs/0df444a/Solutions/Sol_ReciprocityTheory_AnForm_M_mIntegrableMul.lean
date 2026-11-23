-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.mIntegrableMul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:06.574596+00:00
-- url     : https://prove2.me/submissions/536ab2c2-d393-4003-b5ff-6b9046df4954

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
section helpers
variable {e : ℕ} {X : Type} [TopologicalSpace X]
end helpers
private theorem mIntegrable_continuous_mul {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (g c : X → ℝ) (hg : MIntegrable A Φ g) (hc : Continuous c) :
    MIntegrable A Φ (fun x => c x * g x) := by
  intro j K hKt hK
  have hcK : ContinuousOn (fun y => c ((A.chart j).symm y)) K :=
    (hc.comp_continuousOn (A.chart j).continuousOn_symm).mono hKt
  simpa only [mul_assoc] using IntegrableOn.continuousOn_mul hcK (hg j K hKt hK) hK
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : MIntegrableMulStatement := by
  intro e X _ A Φ g c hg hc
  exact mIntegrable_continuous_mul A Φ g c hg hc
end ReciprocityTheory.AnForm.M
