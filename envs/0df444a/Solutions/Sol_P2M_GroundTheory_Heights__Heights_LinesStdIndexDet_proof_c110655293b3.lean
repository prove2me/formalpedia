-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesStdIndexDet_proof_c110655293b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:36:56.55294+00:00
-- url     : https://prove2.me/submissions/2ea613d0-1237-49bc-b60b-355e496451e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesStdIndexDet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesStdIndexDet_span_toAddSubgroup_eq_closure_4928e3faf5ca

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
open NumberField Matrix
open scoped Pointwise
noncomputable section
open KLinesStdIndexDet
namespace GroundTheory.Heights₂.Heights
namespace LinesStdIndexDet
theorem _root_.solution (h1 : LinesGenIndexDet.Statement) : LinesStdIndexDet.Statement := by
  classical
  intro K _ _ k V hV
  let B0 : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin k) ℚ (Fin k → K) :=
    (integralBasis K).smulTower (Pi.basisFun K (Fin k))
  have hB0 : ∀ p, B0 p = integralBasis K p.1 • (Pi.single p.2 1 : Fin k → K) := by
    intro p
    simp only [B0, Module.Basis.smulTower_apply, Pi.basisFun_apply]
  let Ve : (Fin k → K) ≃ₗ[K] (Fin k → K) :=
    Matrix.toLinearEquiv' V (Matrix.invertibleOfIsUnitDet V (Ne.isUnit hV))
  have hVe : ∀ v, Ve v = V *ᵥ v := fun v => rfl
  let Vq : (Fin k → K) ≃ₗ[ℚ] (Fin k → K) := Ve.restrictScalars ℚ
  have hA : (stdLattice K k).toAddSubgroup = AddSubgroup.closure (Set.range B0) := by
    have := span_toAddSubgroup_eq_closure K k LinearMap.id
    simp only [LinearMap.id_apply] at this
    rw [stdLattice, this]
    exact congrArg (fun s => AddSubgroup.closure s)
      (congrArg Set.range (funext fun p => (hB0 p).symm))
  have hB : (Submodule.span (𝓞 K)
        (Set.range fun j => V *ᵥ (Pi.single j 1 : Fin k → K))).toAddSubgroup =
      AddSubgroup.closure (Set.range (B0.map Vq)) := by
    have := span_toAddSubgroup_eq_closure K k (Matrix.toLin' V)
    simp only [Matrix.toLin'_apply] at this
    rw [this]
    refine congrArg (fun s => AddSubgroup.closure s)
      (congrArg Set.range (funext fun p => ?_))
    rw [Module.Basis.map_apply, hB0]
    change _ = Ve _
    rw [map_smul, hVe]
  rw [h1 (Fin k → K) _ B0 (B0.map Vq) _ _ hA hB]
  have hdet : B0.det (B0.map Vq) = Algebra.norm ℚ V.det := by
    have hc : (⇑(B0.map Vq) : _ → Fin k → K) = (Vq : (Fin k → K) →ₗ[ℚ] (Fin k → K)) ∘ B0 := by
      funext p
      rfl
    rw [hc, Module.Basis.det_comp, Module.Basis.det_self, mul_one]
    have hq : (Vq : (Fin k → K) →ₗ[ℚ] (Fin k → K)) = (Matrix.toLin' V).restrictScalars ℚ := by
      ext v
      rfl
    rw [hq, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  rw [hdet]
end LinesStdIndexDet
end GroundTheory.Heights₂.Heights
