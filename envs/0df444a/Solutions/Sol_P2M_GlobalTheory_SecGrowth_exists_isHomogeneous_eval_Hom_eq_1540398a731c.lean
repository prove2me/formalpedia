-- Prove2me | solution 1 for P2M_GlobalTheory_SecGrowth_exists_isHomogeneous_eval_Hom_eq_1540398a731c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:39:31.85373+00:00
-- url     : https://prove2.me/submissions/6a60c31f-14dd-4faf-9d18-11d8f4e7c685

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteOfNotLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.SecGrowth
variable {σ R A : Type} [CommRing R] [CommRing A]
namespace GlobalTheory.SecGrowth
theorem _root_.solution (c : R →+* A) (x : σ → A) (i : σ) (hi : x i = 1)
    (p : MvPolynomial σ R) {t : ℕ} (hp : p.totalDegree ≤ t) :
    ∃ F : MvPolynomial σ R, F.IsHomogeneous t ∧
      MvPolynomial.eval₂Hom c x F = MvPolynomial.eval₂Hom c x p := by
  refine ⟨∑ d ∈ Finset.range (p.totalDegree + 1),
    MvPolynomial.homogeneousComponent d p * MvPolynomial.X i ^ (t - d), ?_, ?_⟩
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun d hd => ?_
    have h := (MvPolynomial.homogeneousComponent_isHomogeneous d p).mul
      (MvPolynomial.isHomogeneous_X_pow (R := R) i (t - d))
    have hd' := Finset.mem_range.1 hd
    rwa [show d + (t - d) = t by omega] at h
  · conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent p]
    simp only [map_sum, map_mul, map_pow, MvPolynomial.eval₂Hom_X', hi, one_pow, _root_.mul_one]
end GlobalTheory.SecGrowth
