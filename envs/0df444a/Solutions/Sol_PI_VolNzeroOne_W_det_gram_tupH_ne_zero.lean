-- Prove2me | solution 1 for PI.VolNzeroOne.W.det_gram_tupH_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:29:35.406958+00:00
-- url     : https://prove2.me/submissions/a7cb9882-5f64-4b21-8d03-883810eb8253

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolNzeroOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NilpotentVolumeOne_LinearIndependentFrameWithNormal
import Theorems.Thm_PI_VolNzeroOne_W_coord_zero_of_row
import Theorems.Thm_PI_VolNzeroOne_W_row_f
import Theorems.Thm_PI_VolNzeroOne_W_herm_wCell_last_mul_mulVec_eq_of_inWb
import Theorems.Thm_PI_VolNzeroOne_W_row_e

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
    (hT1 : ∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) :
    (gramE σ J (tupH P)).det ≠ 0 := by
  have hTne : algebraMap F E (-T) ≠ 0 := by
    rw [map_neg, neg_ne_zero]
    exact (map_ne_zero (algebraMap F E)).mpr hP.2.2.2.2.2.2
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  funext j
  induction j using Fin.addCases with
  | left k =>
    induction k using Fin.lastCases with
    | last => exact coord_zero_of_row _ v hv _ _ _ hTne (herm_wCell_last_mul_mulVec_eq_of_inWb σ J P T hP hT1)
    | cast c => exact coord_zero_of_row _ v hv _ _ 1 one_ne_zero (row_f σ J P T hP hT1 c)
  | right b => exact coord_zero_of_row _ v hv _ _ 1 one_ne_zero (row_e σ J P T hP b)
end PI.VolNzeroOne.W
