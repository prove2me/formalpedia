-- Prove2me | solution 1 for PI.VolNzeroOne.W.row_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:08.824835+00:00
-- url     : https://prove2.me/submissions/e8831788-1828-4f6f-b946-55eb83b9e4f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolNzeroOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NilpotentVolumeOne_LinearIndependentFrameWithNormal
import Theorems.Thm_PI_VolNzeroOne_W_tupH_e
import Theorems.Thm_PI_VolNzeroOne_W_tupH_alt
import Theorems.Thm_PI_VolNzeroOne_W_tupH_f
import Theorems.Thm_PI_VolNzeroOne_W_if_ne_ie
import Theorems.Thm_PI_VolNzeroOne_W_if_ne_iz
import Theorems.Thm_PI_VolNzeroOne_W_if_inj

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
theorem _root_.solution (hP : P.IsStd σ J T) (a : Fin r) :
    ∀ j, gramE σ J (tupH P) (Fin.castAdd r (Fin.castSucc a)) j =
      if j = Fin.natAdd (r + 1) a then 1 else 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
  intro j
  induction j using Fin.addCases with
  | left k =>
    induction k using Fin.lastCases with
    | last =>
      simp only [gramE, tupH_e, tupH_alt]
      rw [h4 a, if_neg (fun h => if_ne_iz a h.symm)]
    | cast c =>
      simp only [gramE, tupH_e]
      rw [h1 a c, if_neg (fun h => if_ne_ie a c h.symm)]
  | right b =>
    simp only [gramE, tupH_e, tupH_f]
    rw [h3 a b]
    by_cases hab : a = b
    · subst hab
      simp
    · rw [if_neg hab, if_neg (fun h => hab (if_inj h).symm)]
end PI.VolNzeroOne.W
