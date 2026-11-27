-- Prove2me | solution 1 for PI.AprimeInfW.map_mulR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:14:26.845722+00:00
-- url     : https://prove2.me/submissions/07cb5f8f-be95-417e-8429-b8fbd89d121a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_TupPlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
import Theorems.Thm_PI_AprimeInfW_mulRC_apply
import Theorems.Thm_PI_AprimeInfW_det_mulRC_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Matrix
variable {r m : ℕ}
namespace PI.AprimeInfW
theorem _root_.solution (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.det ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin r × Fin m × Bool))).map
        (fun y => reim (Matrix.of ((reimE (r := r)).symm y) * A)) =
      ENNReal.ofReal (Complex.normSq A.det ^ r)⁻¹ • volume := by
  set F : EuclideanSpace ℝ (Fin r × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin r × Fin m × Bool) :=
    (reimE (r := r)).toLinearMap ∘ₗ ((mulRC (r := r) A).restrictScalars ℝ) ∘ₗ (reimE (r := r)).symm.toLinearMap
    with hF
  have hdet : F.det = Complex.normSq A.det ^ r := by
    rw [hF, LinearMap.det_conj, det_mulRC_real]
  have hpos : 0 < Complex.normSq A.det ^ r := pow_pos (Complex.normSq_pos.2 hA) _
  have hfun : (fun y => reim (Matrix.of ((reimE (r := r)).symm y) * A)) = F := by
    funext y
    simp only [hF, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars]
    rw [mulRC_apply]
    rfl
  have h := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin r × Fin m × Bool)))) (f := F) (by rw [hdet]; exact hpos.ne')
  rw [hfun, h, hdet, abs_of_pos (inv_pos.2 hpos)]
end PI.AprimeInfW
