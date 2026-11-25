-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_det_gram_cons_add_ebe2c8ece1c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:56:56.840857+00:00
-- url     : https://prove2.me/submissions/e2ffefd8-f952-4c73-973d-eb6917071792

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_gram_comb_ddeda5d33b52

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
open Module Submodule Matrix
open scoped RealInnerProductSpace
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
omit [FiniteDimensional ℝ W]
namespace GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
theorem _root_.solution {m : ℕ} (v : W) (c : Fin m → W) (t : Fin m → ℝ) :
    (gram ℝ (Fin.cons v (fun i => c i + t i • v) : Fin (m + 1) → W)).det =
      (gram ℝ (Fin.cons v c : Fin (m + 1) → W)).det := by
  let T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    Matrix.of fun i j => if i = j then 1 else if j = 0 then (Fin.cons 0 t : Fin (m + 1) → ℝ) i else 0
  have hT : (Fin.cons v (fun i => c i + t i • v) : Fin (m + 1) → W) =
      fun i => ∑ j, T i j • (Fin.cons v c : Fin (m + 1) → W) j := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · have h0 : ∀ x : Fin m, (0 : Fin (m + 1)) ≠ x.succ := fun x => (Fin.succ_ne_zero x).symm
      rw [Fin.sum_univ_succ]
      simp [T, Fin.succ_ne_zero, h0]
    · rw [Fin.sum_univ_succ]
      simp [T, Fin.succ_ne_zero, add_comm]
  have hdet : T.det = 1 := by
    rw [det_of_isLowerTriangular T ?_]
    · simp [T]
    · intro i j hij
      have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      have hj : j ≠ 0 := by
        rintro rfl
        exact absurd hij' (Fin.not_lt_zero i)
      simp [T, hij'.ne, hj]
  rw [hT, gram_comb, det_mul, det_mul, det_transpose, hdet]
  ring
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
