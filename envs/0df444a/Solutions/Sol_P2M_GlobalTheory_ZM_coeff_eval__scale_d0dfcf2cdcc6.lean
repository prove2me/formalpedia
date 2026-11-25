-- Prove2me | solution 1 for P2M_GlobalTheory_ZM_coeff_eval__scale_d0dfcf2cdcc6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:17:41.775947+00:00
-- url     : https://prove2.me/submissions/001a7bed-d0cf-45ef-8ff3-f1eef364a4fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SpMapCompRingHomComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.ZM
private theorem eval₂_monomial_X_mul_C_eq_C_mul_X_pow_degree {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R')
    (w : σ → R') (u : σ →₀ ℕ) (a : R) :
    MvPolynomial.eval₂ ((Polynomial.C : R' →+* Polynomial R').comp β) (fun i => Polynomial.X * Polynomial.C (w i))
        (MvPolynomial.monomial u a) =
      Polynomial.C (MvPolynomial.eval₂ β w (MvPolynomial.monomial u a)) * Polynomial.X ^ u.degree := by
  simp only [MvPolynomial.eval₂_monomial, RingHom.comp_apply, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← Polynomial.C_pow, ← map_prod, map_mul, Finsupp.degree_apply]
  ring
end GlobalTheory.ZM
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM
namespace GlobalTheory.ZM
theorem _root_.solution {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R') (w : σ → R')
    (F : MvPolynomial σ R) (e : ℕ) :
    (MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F).coeff e =
      MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) := by
  refine MvPolynomial.induction_on' F (fun u a => ?_) (fun p q hp hq => ?_)
  · simp only [MvPolynomial.coe_eval₂Hom]
    rw [eval₂_monomial_X_mul_C_eq_C_mul_X_pow_degree, Polynomial.coeff_C_mul_X_pow,
      MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).2
        (MvPolynomial.isHomogeneous_monomial a rfl))]
    split_ifs <;> simp
  · simp only [map_add, Polynomial.coeff_add, hp, hq]
end GlobalTheory.ZM
