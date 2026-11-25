-- Prove2me | solution 1 for PI.FJMX.wtVec2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:59:35.72991+00:00
-- url     : https://prove2.me/submissions/c293cff3-019e-4a1c-9ee5-888c5ed272cd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistPad
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsDiagonalBlockIndexRightOfPositiveRoot
import Theorems.Thm_PI_FJMX_monomialRightWeight_eq_weight_sub
import Theorems.Thm_PI_FJMX_hwVec_hom
import Theorems.Thm_PI_FJMX_negPart_pw
import Theorems.Thm_PI_FJMX_pad_getD
import Theorems.Thm_PI_FJMX_posPart_pw
import Theorems.Thm_PI_FJMX_shapeProd_hom_col
import Theorems.Thm_PI_FJMX_shapeProd_hom_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
variable {p q r s : ℕ}
namespace PI.FJMX
theorem _root_.solution (a b c d : List ℤ) (hd : ShapeData p q r s a b c d) (y : Ix r s) :
    ∃ W : ℤ, (W : ℚ) + sh2 p q r s y = wtOf2 p q r s a b c d y ∧
      ∀ m, coeff m (hwVec p q r s a b c d) ≠ 0 → wt2 m y = W := by
  obtain ⟨ha, hc, hb, hdd, hpa, hpb, hpc, hpd, h1, h2, h3, h4⟩ := hd
  cases y with
  | inl k₀ =>
    have hP := hwVec_hom (p := p) (q := q) (r := r) (s := s) (rightPositiveIndicator (Sum.inl k₀)) a b c d _ 0 0 0
      (shapeProd_hom_col _ _ _ k₀ (fun i k => by simp [rightPositiveIndicator, linePos]) _ (posPart_pw a hpa))
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [rightPositiveIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun j l => by simp [rightPositiveIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun j k => by simp [rightPositiveIndicator, linePos]) _)
    have hN := hwVec_hom (p := p) (q := q) (r := r) (s := s) (rightNegativeIndicator (Sum.inl k₀)) a b c d 0 0 0 _
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [rightNegativeIndicator, linePos]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [rightNegativeIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun j l => by simp [rightNegativeIndicator]) _)
      (shapeProd_hom_col _ _ _ (Fin.rev k₀) (fun j k => by simp [rightNegativeIndicator, linePos, Fin.rev_eq_iff]) _
        (negPart_pw d hpd))
    refine ⟨((posPart a).getD k₀ 0 : ℤ) - ((negPart d).getD (Fin.rev k₀).val 0 : ℤ), ?_, ?_⟩
    · have hv : (Fin.rev k₀).val = r - 1 - k₀.val := by simp [Fin.val_rev]; omega
      simp only [wtOf2, ofBlocks]
      rw [pad_getD a d r h3 ha hdd k₀.val k₀.isLt, hv]
      push_cast
      ring
    · intro m hm
      rw [monomialRightWeight_eq_weight_sub, hP hm, hN hm]
      simp
  | inr l₀ =>
    have hP := hwVec_hom (p := p) (q := q) (r := r) (s := s) (rightPositiveIndicator (Sum.inr l₀)) a b c d 0 0 _ 0
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [rightPositiveIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [rightPositiveIndicator, linePos]) _)
      (shapeProd_hom_col _ _ _ l₀ (fun j l => by simp [rightPositiveIndicator, linePos]) _ (posPart_pw c hpc))
      (shapeProd_hom_zero _ _ _ (fun j k => by simp [rightPositiveIndicator]) _)
    have hN := hwVec_hom (p := p) (q := q) (r := r) (s := s) (rightNegativeIndicator (Sum.inr l₀)) a b c d 0 _ 0 0
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [rightNegativeIndicator]) _)
      (shapeProd_hom_col _ _ _ (Fin.rev l₀) (fun i l => by simp [rightNegativeIndicator, linePos, Fin.rev_eq_iff]) _
        (negPart_pw b hpb))
      (shapeProd_hom_zero _ _ _ (fun j l => by simp [rightNegativeIndicator, linePos]) _)
      (shapeProd_hom_zero _ _ _ (fun j k => by simp [rightNegativeIndicator]) _)
    refine ⟨((posPart c).getD l₀ 0 : ℤ) - ((negPart b).getD (Fin.rev l₀).val 0 : ℤ), ?_, ?_⟩
    · have hv : (Fin.rev l₀).val = s - 1 - l₀.val := by simp [Fin.val_rev]; omega
      simp only [wtOf2, ofBlocks]
      rw [pad_getD c b s h4 hc hb l₀.val l₀.isLt, hv]
      push_cast
      ring
    · intro m hm
      rw [monomialRightWeight_eq_weight_sub, hP hm, hN hm]
      simp
end PI.FJMX
