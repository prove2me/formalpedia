-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isMultiHomog_det_pderiv_over_00a9f6074cf5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:21:22.708444+00:00
-- url     : https://prove2.me/submissions/95afa494-c5d5-47df-92b3-e0189431c56e

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_GenSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinorA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_MultiHomogZ_isMultiHomog_of_blkWtZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_MultiHomogZ_isWeightedHomogeneous_blkWtZ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_MultiHomogZ_isWeightedHomogeneous_pderiv_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {R : Type} [CommRing R]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {s c : ℕ} (G : Fin s → MRingOver R ι)
    (hG : ∀ i, ∃ a, IsMultiHomog (G i) a) (a : Fin c → Fin s) (b : Fin c → Σ k, ι k) :
    ∃ d, IsMultiHomog (Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i)))) d := by
  choose dG hdG using hG
  refine ⟨_, isMultiHomog_of_blkWtZ (n := fun k =>
    ∑ i, ((dG (a i) k : ℤ) - blkWtZ k (b i))) fun k => ?_⟩
  rw [Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have hp : IsWeightedHomogeneous (blkWtZ (ι := ι) k)
      (∏ i, (Matrix.of fun i j => pderiv (b j) (G (a i))) (σ i) i)
      (∑ i, ((dG (a (σ i)) k : ℤ) - blkWtZ k (b i))) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ =>
      isWeightedHomogeneous_pderiv_int (isWeightedHomogeneous_blkWtZ (hdG (a (σ i))) k) (b i)
  have e : ∑ i, ((dG (a (σ i)) k : ℤ) - blkWtZ k (b i)) = ∑ i, ((dG (a i) k : ℤ) - blkWtZ k (b i)) := by
    simp only [Finset.sum_sub_distrib]
    congr 1
    exact Equiv.sum_comp σ (fun i => (dG (a i) k : ℤ))
  rw [e] at hp
  rw [Units.smul_def, zsmul_eq_mul, ← map_intCast (C : R →+* MRingOver R ι), ← zero_add (∑ i, _)]
  exact (isWeightedHomogeneous_C _ _).mul hp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
