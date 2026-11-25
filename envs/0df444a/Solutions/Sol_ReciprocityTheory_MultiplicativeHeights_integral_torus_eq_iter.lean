-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.integral_torus_eq_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:45:32.007387+00:00
-- url     : https://prove2.me/submissions/9cccc423-61ad-4efa-a9ae-7959f1180af2

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurePreserving_update_torus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) {g : (ι → ℝ) → ℝ}
    (hg : Integrable g (torusProb ι)) :
    Integrable (fun x => ∫ t in Set.Ioc (0 : ℝ) 1, g (Function.update x i t)) (torusProb ι) ∧
    ∫ θ, g θ ∂(torusProb ι) =
      ∫ x, (∫ t in Set.Ioc (0 : ℝ) 1, g (Function.update x i t)) ∂(torusProb ι) := by
  have hU := measurePreserving_update_torus (ι := ι) i
  have hgU : Integrable (g ∘ fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
      ((torusProb ι).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    (hU.integrable_comp hg.aestronglyMeasurable).mpr hg
  refine ⟨hgU.integral_prod_left, ?_⟩
  have h1 : ∫ θ, g θ ∂(torusProb ι) = ∫ p, g (Function.update p.1 i p.2)
      ∂((torusProb ι).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    conv_lhs => rw [← hU.map_eq]
    exact integral_map hU.measurable.aemeasurable (by rw [hU.map_eq]; exact hg.aestronglyMeasurable)
  rw [h1]
  exact integral_prod _ hgU
end ReciprocityTheory.MultiplicativeHeights
