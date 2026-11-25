-- Prove2me | solution 1 for PI.LevelKSplit.W.ExC.dual_frame_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:06:42.66378+00:00
-- url     : https://prove2.me/submissions/ffdb9afa-76c4-49be-99be-7b90533ef776

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Theorems.Thm_PI_LevelKSplit_W_ExC_hE_smul_left
import Theorems.Thm_PI_LevelKSplit_W_ExC_dual_e
import Theorems.Thm_PI_LevelKSplit_W_Glob_hE_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.ExC
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit PI.LevelKSplit.W.Glob
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
namespace PI.LevelKSplit.W.ExC
theorem _root_.solution (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) {r : ℕ} (P : Frame E n r) (T : F)
    (hP : P.IsStd σ J T) (a a' : Fin (r + 1)) :
    hE σ J (dualFrameAlt P T a') (F0 P a) = if a = a' then 1 else 0 := by
  have hc : σ (algebraMap F E (-T)⁻¹) = algebraMap F E (-T)⁻¹ := σ.commutes _
  induction a using Fin.lastCases with
  | last =>
    induction a' using Fin.lastCases with
    | last =>
      simp only [dualFrameAlt, F0, Fin.snoc_last, hE_smul_left, hc, if_true]
      rw [hP.2.2.2.2.2.1, ← map_mul, inv_mul_cancel₀ (neg_ne_zero.2 hP.2.2.2.2.2.2), map_one]
    | cast j =>
      simp only [dualFrameAlt, F0, Fin.snoc_last, Fin.snoc_castSucc, hP.2.2.2.2.1 j]
      rw [if_neg (fun h => Fin.castSucc_ne_last j h.symm)]
  | cast i =>
    induction a' using Fin.lastCases with
    | last =>
      simp only [dualFrameAlt, F0, Fin.snoc_last, Fin.snoc_castSucc, hE_smul_left]
      rw [hE_swap hJ hinv, hP.2.2.2.1 i, map_zero, mul_zero]
      simp [Fin.castSucc_ne_last]
    | cast j =>
      simp only [dualFrameAlt, F0, Fin.snoc_castSucc, Fin.castSucc_inj]
      exact dual_e hJ hinv P T hP i j
end PI.LevelKSplit.W.ExC
