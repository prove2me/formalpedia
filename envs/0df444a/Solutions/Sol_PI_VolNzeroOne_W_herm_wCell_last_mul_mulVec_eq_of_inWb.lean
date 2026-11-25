-- Prove2me | solution 1 for PI.VolNzeroOne.W.herm_wCell_last_mul_mulVec_eq_of_inWb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:48:49.196998+00:00
-- url     : https://prove2.me/submissions/35692dd0-8e4f-47f7-b68d-b97069e48a7c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolNzeroOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NilpotentVolumeOne_LinearIndependentFrameWithNormal
import Theorems.Thm_PI_VolNzeroOne_W_tupH_e
import Theorems.Thm_PI_VolNzeroOne_W_tupH_alt
import Theorems.Thm_PI_VolNzeroOne_W_tupH_f
import Theorems.Thm_PI_VolNzeroOne_W_iz_ne_ie
import Theorems.Thm_PI_VolNzeroOne_W_if_ne_iz

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
    ∀ j, gramE σ J (tupH P) (Fin.castAdd r (Fin.last r)) j =
      if j = Fin.castAdd r (Fin.last r) then algebraMap F E (-T) else 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
  intro j
  induction j using Fin.addCases with
  | left k =>
    induction k using Fin.lastCases with
    | last =>
      simp only [gramE, tupH_alt]
      rw [h6]
      simp
    | cast c =>
      rw [← hT1]
      simp only [gramE, tupH_e, tupH_alt]
      rw [h4 c, map_zero, if_neg (fun h => iz_ne_ie c h.symm)]
  | right b =>
    rw [← hT1]
    simp only [gramE, tupH_alt, tupH_f]
    rw [h5 b, map_zero, if_neg (if_ne_iz b)]
end PI.VolNzeroOne.W
