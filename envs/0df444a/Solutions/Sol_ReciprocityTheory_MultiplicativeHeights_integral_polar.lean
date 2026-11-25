-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.integral_polar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:06:07.635933+00:00
-- url     : https://prove2.me/submissions/79fe93ae-6a55-459e-a9dc-a82a91d47140

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_finrank_euclidean_complex
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
theorem _root_.solution {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℂ (Fin n) → ℝ) :
    ∫ x, f x = ∫ p : UnitSphereC n × Ioi (0 : ℝ), f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n)))
      ∂((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1))) := by
  rw [← (Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))).integral_comp
      (homeomorphUnitSphereProd _).measurableEmbedding
      (fun p : UnitSphereC n × Ioi (0 : ℝ) ↦ f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n))))]
  simp only [homeomorphUnitSphereProd_smul_eq]
  rw [integral_subtype_comap (measurableSet_singleton 0).compl
    (fun x : EuclideanSpace ℂ (Fin n) ↦ f x)]
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclidean_complex]; omega)
  rw [Measure.restrict_congr_set (show ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))) =ᵐ[volume] univ from
    ae_eq_univ.mpr (by rw [compl_compl]; exact measure_singleton 0)), Measure.restrict_univ]
end ReciprocityTheory.MultiplicativeHeights
