-- Prove2me | solution 1 for PI.VolNzeroOne.W.gram_frame_with_normal_eq_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:18:23.422665+00:00
-- url     : https://prove2.me/submissions/4cb58675-7b90-4e89-be11-3d0a61154107

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolNzeroOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NilpotentVolumeOne_LinearIndependentFrameWithNormal
import Theorems.Thm_PI_VolNzeroOne_W_frameInitialVectors_castSucc
import Theorems.Thm_PI_VolNzeroOne_W_frameInitialVectors_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolNzeroOne PI.VolNzeroOne.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {M r : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (P : Frame E M r) (T : F)
namespace PI.VolNzeroOne.W
theorem _root_.solution (hP : P.IsStd σ J T)
    (hT0 : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j) :
    ∀ i j, gramE σ J (F0 P) i j =
      if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
  intro i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [gramE, frameInitialVectors_last]
      rw [h6]
      simp
    | cast b =>
      rw [← hT0]
      simp only [gramE, frameInitialVectors_last, frameInitialVectors_castSucc]
      rw [h4 b, map_zero]
      simp [(Fin.castSucc_lt_last b).ne]
  | cast a =>
    induction j using Fin.lastCases with
    | last =>
      simp only [gramE, frameInitialVectors_last, frameInitialVectors_castSucc]
      rw [h4 a]
      simp [(Fin.castSucc_lt_last a).ne]
    | cast b =>
      simp only [gramE, frameInitialVectors_castSucc]
      rw [h1 a b]
      simp [(Fin.castSucc_lt_last a).ne]
end PI.VolNzeroOne.W
