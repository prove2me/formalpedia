-- Prove2me | solution 1 for P2M_GlobalTheory_eval__scale_of_isHomogeneous_ea2ff51b767f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:34:38.90312+00:00
-- url     : https://prove2.me/submissions/57149750-1e52-467f-b032-a41665786703

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DehomogenisationIsRadicalAndTorsionFree

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {o σ S : Type} [CommRing o] [CommRing S] (f : o →+* S)
    (g : σ → S) (u : S) {F : MvPolynomial σ o} {e : ℕ} (hF : F.IsHomogeneous e) :
    MvPolynomial.eval₂ f (fun j => g j * u) F = MvPolynomial.eval₂ f g F * u ^ e := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hF.degree_eq_sum_deg_support hd, ← Finset.prod_pow_eq_pow_sum, _root_.mul_assoc,
    ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun j _ => mul_pow _ _ _
end GlobalTheory
