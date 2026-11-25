-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereIntegrable_log_6df905eb445b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:49:07.466802+00:00
-- url     : https://prove2.me/submissions/36497d78-9141-438b-b84e-07952b1e604a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_integrableOn_log_mahler_2b6fa8e526b5


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
open MvPolynomial MeasureTheory ProbabilityTheory Real
noncomputable section
open GroundTheory.Heights₂.Heights.PointwiseLelong
variable {N : ℕ}
namespace GroundTheory.Heights₂.Heights.PointwiseLelong
theorem _root_.solution {Q : MvPolynomial (Fin N) ℂ} (hQ : Q ≠ 0) :
    SphereIntegrable (HermNorm.std N) 1 (fun u ↦ Real.log ‖eval (fun j ↦ u (0, j)) Q‖) := by
  have hinj : Function.Injective (fun j : Fin N => ((0 : Fin 1), j)) :=
    fun a b h => (Prod.ext_iff.mp h).2
  have h0 : rename (fun j : Fin N => ((0 : Fin 1), j)) Q ≠ 0 := by
    intro h
    exact hQ (rename_injective _ hinj (by rw [h, map_zero]))
  have := (LogInt.integrableOn_log_mahler (HermNorm.std N) _ h0).1
  simp only [eval_rename, Function.comp_def] at this
  exact this
end GroundTheory.Heights₂.Heights.PointwiseLelong
