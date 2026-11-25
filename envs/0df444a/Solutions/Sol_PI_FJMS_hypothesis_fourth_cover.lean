-- Prove2me | solution 1 for PI.FJMS.hypothesis_fourth_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:11.158244+00:00
-- url     : https://prove2.me/submissions/90969107-d75c-4a70-a952-5c3eb5eb0651

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsBlockHighestWeight
import Theorems.Thm_PI_FJMS_segs_of
import Theorems.Thm_PI_FJMS_blkHyp_neg
import Theorems.Thm_PI_FJMS_idxN
import Theorems.Thm_PI_FJMS_neg_of_lt


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
theorem _root_.solution : HypD := by
  intro p q r s μ μ' P hM
  obtain ⟨-, -, -, sR1n, -, sL2n, -, -⟩ := segs_of hM
  refine blkHyp_neg hM (fun i => (Sum.inr (Fin.rev (Fin.castLE (nN_le _) i)) : Ix p q))
    (fun k => (Sum.inl (Fin.rev (Fin.castLE (nN_le _) k)) : Ix r s))
    (Sum.inr_injective.comp (Fin.rev_injective.comp (Fin.castLE_injective _)))
    (Sum.inl_injective.comp (Fin.rev_injective.comp (Fin.castLE_injective _)))
    (fun a b h => ?_) (fun c d h => ?_)
    (fun a b c => by cases c <;> rfl) (fun c d a => by cases a <;> rfl) (fun i k => rfl)
    (fun i c h1 h2 => ?_) (fun k a h1 h2 => ?_)
    (fun i => neg_of_lt (leftWeightSecond p q r s μ) sR1n i) (fun k => neg_of_lt (rightWeightFirst p q r s μ') sL2n k)
    _ _ (fun i => rfl) (fun k => rfl)
  · have h' : a.val < b.val := h
    have := b.isLt
    have := nN_le (leftWeightSecond p q r s μ)
    simp only [posC, Fin.lt_def, Fin.val_rev, Fin.val_castLE]
    omega
  · have h' : c.val < d.val := h
    have := d.isLt
    have := nN_le (rightWeightFirst p q r s μ')
    simp only [posC, Fin.lt_def, Fin.val_rev, Fin.val_castLE]
    omega
  · cases c with
    | inl c =>
      obtain ⟨x, hx⟩ := idxN (rightWeightFirst p q r s μ') sL2n c h2
      exact ⟨x, by simp only [hx]⟩
    | inr c => simp [linePos] at h1
  · cases a with
    | inl a => simp [linePos] at h1
    | inr a =>
      obtain ⟨x, hx⟩ := idxN (leftWeightSecond p q r s μ) sR1n a h2
      exact ⟨x, by simp only [hx]⟩
end PI.FJMS
