-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_isMultiHomog_of_isHomogeneous_03061861cacf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:27:31.829726+00:00
-- url     : https://prove2.me/submissions/2ff45fd2-0bfa-4518-aa47-f82bca05759b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POneBlockPointDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
noncomputable section
open GroundTheory.Heights₂.Heights.OneBlockPointDeg
variable {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {k₀ : K}
namespace GroundTheory.Heights₂.Heights.OneBlockPointDeg
theorem _root_.solution (hK : ∀ k, k = k₀) {f : MRingOver Φ ι} {n : ℕ}
    (hf : f.IsHomogeneous n) : IsMultiHomog f fun _ => n := by
  intro m hm k
  have h := hf (mem_support_iff.mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
  rw [Fintype.sum_sigma, Fintype.sum_eq_single k
    (fun k' hk' => absurd ((hK k').trans (hK k).symm) hk')] at h
  exact h
end GroundTheory.Heights₂.Heights.OneBlockPointDeg
