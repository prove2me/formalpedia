-- Prove2me | solution 1 for P2M_GlobalTheory_ZM_DenseFib_eval__scale_1314a053eb26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:04:59.581497+00:00
-- url     : https://prove2.me/submissions/5acf61a2-4997-44c5-b344-6ca45794b2df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MemIdealOfOfDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.DenseFib
namespace GlobalTheory.ZM.DenseFib
theorem _root_.solution {R L σ : Type} [CommRing R] [CommRing L] (φ : R →+* L) (x : σ → L) (c : L)
    {F : MvPolynomial σ R} {e : ℕ} (hF : F.IsHomogeneous e) :
    MvPolynomial.eval₂ φ (fun j => c * x j) F = c ^ e * MvPolynomial.eval₂ φ x F := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = e := by
    have := hF (MvPolynomial.mem_support_iff.1 hd)
    rw [← this]; simp [Finsupp.weight_apply, Finsupp.sum]
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
end GlobalTheory.ZM.DenseFib
