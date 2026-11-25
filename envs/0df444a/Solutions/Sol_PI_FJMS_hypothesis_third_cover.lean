-- Prove2me | solution 1 for PI.FJMS.hypothesis_third_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:35.338058+00:00
-- url     : https://prove2.me/submissions/02173d25-26e2-4a53-a282-660b0d30ae89

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsBlockHighestWeight
import Theorems.Thm_PI_FJMS_segs_of
import Theorems.Thm_PI_FJMS_blkHyp_pos
import Theorems.Thm_PI_FJMS_idxP
import Theorems.Thm_PI_FJMS_pos_of_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMS
open PI.FJM PI.FJMP
namespace PI.FJMS
theorem _root_.solution : HypC := by
  intro p q r s μ μ' P hM
  obtain ⟨-, -, sR1p, -, -, -, sR2p, -⟩ := segs_of hM
  refine blkHyp_pos hM (fun i => (Sum.inr (Fin.castLE (nP_le_nW _) i) : Ix p q))
    (fun k => (Sum.inr (Fin.castLE (nP_le_nW _) k) : Ix r s))
    (Sum.inr_injective.comp (Fin.castLE_injective _)) (Sum.inr_injective.comp (Fin.castLE_injective _))
    (fun a b h => by simp only [posC, Fin.lt_def, Fin.val_castLE]; exact h)
    (fun c d h => by simp only [posC, Fin.lt_def, Fin.val_castLE]; exact h)
    (fun a b c => by cases c <;> rfl) (fun c d a => by cases a <;> rfl) (fun i k => rfl)
    (fun i c h1 h2 => ?_) (fun k a h1 h2 => ?_)
    (fun i => pos_of_lt (leftWeightSecond p q r s μ) sR1p i) (fun k => pos_of_lt (rightWeightSecond p q r s μ') sR2p k)
    _ _ (fun i => rfl) (fun k => rfl)
  · cases c with
    | inl c => simp [linePos] at h1
    | inr c =>
      obtain ⟨x, hx⟩ := idxP (rightWeightSecond p q r s μ') sR2p c h2
      exact ⟨x, by simp only [hx]⟩
  · cases a with
    | inl a => simp [linePos] at h1
    | inr a =>
      obtain ⟨x, hx⟩ := idxP (leftWeightSecond p q r s μ) sR1p a h2
      exact ⟨x, by simp only [hx]⟩
end PI.FJMS
