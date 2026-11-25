-- Prove2me | solution 1 for PI.AprimeInfW.map_mulL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:32.335415+00:00
-- url     : https://prove2.me/submissions/724e1613-6263-4ab0-b4d9-330bbfffd0a7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_TupPlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
import Theorems.Thm_PI_AprimeInfW_mulLC_apply
import Theorems.Thm_PI_AprimeInfW_det_mulLC_real

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
theorem _root_.solution {c : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.det ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin m × Fin c × Bool))).map
        (fun y => reim (A * Matrix.of ((reimE (r := m) (m := c)).symm y))) =
      ENNReal.ofReal (Complex.normSq A.det ^ c)⁻¹ • volume := by
  set F : EuclideanSpace ℝ (Fin m × Fin c × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin c × Bool) :=
    (reimE (r := m) (m := c)).toLinearMap ∘ₗ ((mulLC (c := c) A).restrictScalars ℝ) ∘ₗ
      (reimE (r := m) (m := c)).symm.toLinearMap with hF
  have hdet : F.det = Complex.normSq A.det ^ c := by
    rw [hF, LinearMap.det_conj, det_mulLC_real]
  have hpos : 0 < Complex.normSq A.det ^ c := pow_pos (Complex.normSq_pos.2 hA) _
  have hfun : (fun y => reim (A * Matrix.of ((reimE (r := m) (m := c)).symm y))) = F := by
    funext y
    simp only [hF, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars]
    rw [mulLC_apply]
    rfl
  have h := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin m × Fin c × Bool)))) (f := F) (by rw [hdet]; exact hpos.ne')
  rw [hfun, h, hdet, abs_of_pos (inv_pos.2 hpos)]
end PI.AprimeInfW
