-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_det_gram_cons_orth_73427f220327
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:24.206062+00:00
-- url     : https://prove2.me/submissions/001ad532-6693-4537-8ce9-aff0789f5e05

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt

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
theorem _root_.solution {m : ℕ} (v : W) (c : Fin m → W) (hc : ∀ i, inner ℝ v (c i) = 0) :
    (gram ℝ (Fin.cons v c : Fin (m + 1) → W)).det = ‖v‖ ^ 2 * (gram ℝ c).det := by
  rw [det_succ_row_zero, Fin.sum_univ_succ]
  have h0 : ∀ j : Fin m, gram ℝ (Fin.cons v c : Fin (m + 1) → W) 0 j.succ = 0 := fun j => by
    simp [gram, hc]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  have hsub : (gram ℝ (Fin.cons v c : Fin (m + 1) → W)).submatrix Fin.succ (Fin.succAbove 0) =
      gram ℝ c := by
    ext i j
    simp [gram]
  rw [hsub]
  simp [gram]
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
