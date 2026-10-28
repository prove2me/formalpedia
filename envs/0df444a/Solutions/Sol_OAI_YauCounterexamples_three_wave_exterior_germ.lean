-- Prove2me | solution 1 for OAI.YauCounterexamples.three_wave_exterior_germ
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:38:00.237164+00:00
-- url     : https://prove2.me/submissions/1bf68c8e-c97d-4b42-b0ba-98f3276a95c7

import Mathlib
import Definitions.Def_SmoothYau
import Definitions.Def_OAIQ070A010

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeRobustProfileNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples


section
open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace
lemma threeNormalGlue_tsupport (C : ℝ) {f : NormalWaveSpace → ℝ}
    (hc : HasCompactSupport (fun y => f y-C)) {K : Set NormalWaveSpace}
    (hK : tsupport (fun y => f y-C) ⊆ K) :
    tsupport (fun p => threeNormalGlue C f p-C) ⊆ threeNormalInv '' K := by
  have he : (fun p => threeNormalGlue C f p-C)=
      manifoldChartPush threeProfileCenter ((fun y => f y-C) ∘ threeNormalEquiv.symm) := by
    funext p; simp [threeNormalGlue]
  rw [he]
  intro p hp
  obtain ⟨y,hy,rfl⟩ := manifoldChartPush_tsupport _
    (hc.comp_homeomorph threeNormalEquiv.symm.toHomeomorph)
    (by rw [three_chart_target]; exact subset_univ _) hp
  rw [tsupport_comp_eq_preimage _ threeNormalEquiv.symm.toHomeomorph] at hy
  refine ⟨threeNormalEquiv.symm y,hK hy,?_⟩
  simp [threeNormalInv]
end


open Set Filter Function Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff InnerProductSpace

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ExistsThreeScalarProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma threeWaveLift_tsupport {u : NormalWaveSpace → ℝ} (hc : HasCompactSupport u)
    {K : Set NormalWaveSpace} (hs : tsupport u⊆K) :
    tsupport (threeWaveLift u)⊆threeNormalInv '' K := by
  have he : threeWaveLift u=(fun p => threeNormalGlue 0 u p-0) := by
    funext p; simp [threeWaveLift,threeNormalGlue]
  rw [he]
  exact threeNormalGlue_tsupport 0 (by simpa using hc) (by simpa using hs)
end


open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_SphereMetric_ThreeCutoffControlBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma three_wave_exterior_germ_oai {u : NormalWaveSpace → ℝ} (hc : HasCompactSupport u)
    {r : ℝ} (hs : tsupport u⊆closedBall 0 r) (k : ℕ) {q : ThreeManifold}
    (hq : q∉threeNormalInv '' closedBall 0 r) :
    threeCoupled threeCouplingRadius k+threeWaveLift u =ᶠ[𝓝 q] threeCoupled threeCouplingRadius k := by
  have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hq (threeWaveLift_tsupport hc hs h))
  filter_upwards [hz] with y hy
  simp only [Pi.add_apply,hy,Pi.zero_apply,add_zero]
end


open Set Filter Function Manifold Metric BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.three_wave_exterior_germ_oai := @OAI.YauCounterexamples.three_wave_exterior_germ_oai
