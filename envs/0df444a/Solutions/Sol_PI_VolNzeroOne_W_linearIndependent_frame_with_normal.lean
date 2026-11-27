-- Prove2me | solution 1 for PI.VolNzeroOne.W.linearIndependent_frame_with_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:18:27.261786+00:00
-- url     : https://prove2.me/submissions/7365431d-5fa9-4e97-b96f-9a798cc1aa54

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolNzeroOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NilpotentVolumeOne_LinearIndependentFrameWithNormal
import Theorems.Thm_PI_VolNzeroOne_W_linIndep_of_gram
import Theorems.Thm_PI_VolNzeroOne_W_det_gram_tupH_ne_zero

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
    LinearIndependent E (F0 P) := by
  have h := linIndep_of_gram σ J (tupH P) (det_gram_tupH_ne_zero σ J P T hP hT1)
  have he : F0 P = tupH P ∘ Fin.castAdd r := by
    funext i
    simp [tupH]
  rw [he]
  exact h.comp _ (Fin.castAdd_injective _ _)
end PI.VolNzeroOne.W
