-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TangentGaussInvariant_proof_075d9f73ece7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:09:28.042731+00:00
-- url     : https://prove2.me/submissions/18ba8e73-03c9-4175-a524-bce36cb7ef43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussInvariant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linProj_matSub_fd6597c80c86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_matGauss_matSub_099f3ef8c5f3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_unitary_leadCoordPlane_64ab9545e835

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
open MeasureTheory Module
open scoped Matrix
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace TangentGaussInvariant
theorem _root_.solution : TangentGaussInvariant.Statement := by
  intro n m hm hmn T hT y hy
  obtain ⟨U, hLT, hTL, hUy⟩ := exists_unitary_leadCoordPlane hm hmn T hT y hy
  set L := leadCoordPlane n m with hL
  let W : L →ₗᵢ[ℂ] T :=
    { toFun := fun x => ⟨U x, hLT x x.2⟩
      map_add' := fun x x' => by ext1; simp
      map_smul' := fun c x => by ext1; simp
      norm_map' := fun x => by simp }
  have hWx : ∀ x : L, (W x : EuclideanSpace ℂ (Fin n)) = U x := fun _ => rfl
  have hWsurj : Function.Surjective W := by
    intro t
    obtain ⟨w, hw, hwt⟩ := hTL t t.2
    exact ⟨⟨w, hw⟩, Subtype.ext hwt⟩
  have hfin : finrank ℂ L = finrank ℂ T :=
    (LinearEquiv.ofBijective W.toLinearMap ⟨W.injective, hWsurj⟩).finrank_eq
  have hJ : ∀ π : Fin m → Fin n → ℂ, tangentJac (matSub U π) L = tangentJac π T := by
    intro π
    have hcomp : (linProjₗ (matSub U π)).comp L.subtype =
        ((linProjₗ π).comp T.subtype).comp W.toLinearMap := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearIsometry.coe_toLinearMap,
        hWx]
      exact linProj_matSub U π x
    unfold tangentJac
    have h2 := LinearMap.normDet_comp_of_finrank_eq (𝕜 := ℂ) (U := L) (V := T)
      (W := EuclideanSpace ℂ (Fin m)) W.toLinearMap ((linProjₗ π).comp T.subtype) (by exact hfin)
    rw [hcomp, h2, LinearIsometry.normDet_eq_one, mul_one]
  have hemb : MeasurableEmbedding (matSub (m := m) U) := (matSubEquiv U).measurableEmbedding
  have key := (measurePreserving_matSub (m := m) U).lintegral_comp_emb hemb
    (fun π => matGauss π *
      (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
        (linProj π (((‖y‖ : ℝ) : ℂ) • firstCoordVec n)) *
      ENNReal.ofReal (tangentJac π (leadCoordPlane n m)))
  unfold tangentGaussProfile
  refine Eq.trans ?_ key
  refine lintegral_congr fun π => ?_
  simp only [matGauss_matSub, linProj_matSub, hUy, ← hL, hJ]
end TangentGaussInvariant
end GroundTheory.Heights₂.Heights
