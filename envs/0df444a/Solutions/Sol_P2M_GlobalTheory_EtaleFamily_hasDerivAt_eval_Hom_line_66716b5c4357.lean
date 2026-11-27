-- Prove2me | solution 1 for P2M_GlobalTheory_EtaleFamily_hasDerivAt_eval_Hom_line_66716b5c4357
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:13:36.414871+00:00
-- url     : https://prove2.me/submissions/f9d9bffb-8330-432a-b31c-6b78478dd245

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolomorphicSections

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
open GlobalTheory GlobalTheory.EtaleFamily
namespace GlobalTheory.EtaleFamily
theorem _root_.solution {R J : Type*} [CommRing R] [Fintype J]
    (φ : R →+* ℂ) (q : MvPolynomial J R) (y v : J → ℂ) :
    HasDerivAt (fun t : ℂ => MvPolynomial.eval₂Hom φ (y + t • v) q)
      (∑ i, MvPolynomial.eval₂Hom φ y (MvPolynomial.pderiv i q) * v i) 0 := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (0 : ℂ) (φ a)
  | add P Q hP hQ =>
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    exact hP.add hQ
  | mul_X P i hP =>
    have hX : HasDerivAt (fun t : ℂ => y i + t * v i) (v i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (v i)).const_add (y i)
    have h := hP.mul hX
    simp only [map_mul, MvPolynomial.eval₂Hom_X', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine HasDerivAt.congr_deriv h ?_
    have h1 : ∀ j, MvPolynomial.eval₂Hom φ y (MvPolynomial.pderiv j (P * MvPolynomial.X i)) * v j =
        MvPolynomial.eval₂Hom φ y (MvPolynomial.pderiv j P) * v j * y i +
        if i = j then MvPolynomial.eval₂Hom φ y P * v j else 0 := by
      intro j
      rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
      by_cases hij : i = j
      · subst hij; simp; ring
      · simp [hij, Pi.single_eq_of_ne hij]; ring
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.sum_mul]
    simp
end GlobalTheory.EtaleFamily
