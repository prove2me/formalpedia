-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointArithIntersection_sum_ringHom_restrict_c82ad83b448b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:22.286809+00:00
-- url     : https://prove2.me/submissions/b130df0e-f9ef-4826-be08-2d9703751563

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIsSheetFinZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPointArInt

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.PointArithIntersection
open IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
variable {T : Type} [Fintype T]
variable {K' : Type} [Field K'] [NumberField K']
namespace GroundTheory.Heights₂.Heights.PointArithIntersection
theorem _root_.solution (κ : IntermediateField ℚ K') (H : (κ →ₐ[ℚ] ℂ) → ℝ)
    [Fintype (κ →ₐ[ℚ] ℂ)] :
    ∑ σ : K' →+* ℂ, H ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')) =
      (Module.finrank κ K' : ℝ) * ∑ f, H f := by
  classical
  rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K' ℂ)
    (fun σ : K' →+* ℂ => H ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')))
    (fun σ : K' →ₐ[ℚ] ℂ => H (σ.comp (IsScalarTower.toAlgHom ℚ κ K'))) (fun _ => rfl)]
  let res : (K' →ₐ[ℚ] ℂ) → (κ →ₐ[ℚ] ℂ) := fun σ => σ.comp (IsScalarTower.toAlgHom ℚ κ K')
  rw [← Fintype.sum_fiberwise res, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hconst : ∀ i : {σ // res σ = f}, H (res i) = H f := fun i => by rw [i.2]
  rw [Finset.sum_congr rfl fun i _ => hconst i, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  congr 1
  have e : {σ // res σ = f} ≃ @AlgHom κ K' ℂ _ _ _ _ f.toRingHom.toAlgebra :=
    ((algHomEquivSigma (A := ℚ) (B := κ) (C := K') (D := ℂ)).subtypeEquiv
      (p := fun σ => res σ = f) (q := fun x => x.1 = f) fun σ => Iff.rfl).trans (Equiv.sigmaSubtype f)
  let _ := f.toRingHom.toAlgebra
  rw [Fintype.card_eq_nat_card, Nat.card_congr e,
    AlgHom.natCard_of_splits κ K' ℂ fun _ => IsAlgClosed.splits _]
end GroundTheory.Heights₂.Heights.PointArithIntersection
