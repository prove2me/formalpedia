-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.integrable_polar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:20:24.715555+00:00
-- url     : https://prove2.me/submissions/b62bcb0d-daa6-4fca-ac03-57bdc83a23aa

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric Set Real
private theorem homeomorphUnitSphereProd_smul_eq {n : ℕ} (x : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n)))) :
    ((homeomorphUnitSphereProd _ x).2 : ℝ) •
      ((homeomorphUnitSphereProd _ x).1 : EuclideanSpace ℂ (Fin n)) = x := by
  have hx : ‖(x : EuclideanSpace ℂ (Fin n))‖ ≠ 0 := norm_ne_zero_iff.mpr x.2
  simp [homeomorphUnitSphereProd, homeomorphSphereProd, smul_smul, hx]
end ReciprocityTheory.MultiplicativeHeights
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric Set Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (n : ℕ) {f : EuclideanSpace ℂ (Fin n) → ℝ} (hf : Integrable f) :
    Integrable (fun p : UnitSphereC n × Ioi (0 : ℝ) ↦ f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n))))
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1))) := by
  rw [← (Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))).integrable_comp_emb
      (homeomorphUnitSphereProd _).measurableEmbedding]
  have h2 := (integrableOn_iff_comap_subtypeVal (measurableSet_singleton
    (0 : EuclideanSpace ℂ (Fin n))).compl).mp hf.integrableOn
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, homeomorphUnitSphereProd_smul_eq]
end ReciprocityTheory.MultiplicativeHeights
