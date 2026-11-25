-- Prove2me | solution 1 for PI.FJMX.wtVec1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:01.629802+00:00
-- url     : https://prove2.me/submissions/90991c60-93c7-45be-9ac8-cb10c4d544f2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistPad
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsDiagonalBlockIndexRightOfPositiveRoot
import Theorems.Thm_PI_FJMX_monomialLeftWeight_eq_weight_sub
import Theorems.Thm_PI_FJMX_hwVec_hom
import Theorems.Thm_PI_FJMX_negPart_pw
import Theorems.Thm_PI_FJMX_pad_getD
import Theorems.Thm_PI_FJMX_posPart_pw
import Theorems.Thm_PI_FJMX_shapeProd_hom_row
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
theorem _root_.solution (a b c d : List ℤ) (hd : ShapeData p q r s a b c d) (x : Ix p q) :
    ∃ W : ℤ, (W : ℚ) + sh1 p q r s x = wtOf1 p q r s a b c d x ∧
      ∀ m, coeff m (hwVec p q r s a b c d) ≠ 0 → wt1 m x = W := by
  obtain ⟨ha, hc, hb, hdd, hpa, hpb, hpc, hpd, h1, h2, h3, h4⟩ := hd
  cases x with
  | inl i₀ =>
    have hP := hwVec_hom (p := p) (q := q) (r := r) (s := s) (leftPositiveIndicator (Sum.inl i₀)) a b c d _ 0 0 0
      (shapeProd_hom_row _ _ _ i₀ (fun i k => by simp [leftPositiveIndicator, linePos]) _ (posPart_pw a hpa))
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftPositiveIndicator, linePos]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftPositiveIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftPositiveIndicator]) _)
    have hN := hwVec_hom (p := p) (q := q) (r := r) (s := s) (leftNegativeIndicator (Sum.inl i₀)) a b c d 0 _ 0 0
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [leftNegativeIndicator, linePos]) _)
      (shapeProd_hom_row _ _ _ (Fin.rev i₀) (fun i l => by simp [leftNegativeIndicator, linePos, Fin.rev_eq_iff]) _
        (negPart_pw b hpb))
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftNegativeIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftNegativeIndicator]) _)
    refine ⟨((posPart a).getD i₀ 0 : ℤ) - ((negPart b).getD (Fin.rev i₀).val 0 : ℤ), ?_, ?_⟩
    · have hv : (Fin.rev i₀).val = p - 1 - i₀.val := by simp [Fin.val_rev]; omega
      simp only [wtOf1, ofBlocks]
      rw [pad_getD a b p h1 ha hb i₀.val i₀.isLt, hv]
      push_cast
      ring
    · intro m hm
      rw [monomialLeftWeight_eq_weight_sub, hP hm, hN hm]
      simp
  | inr j₀ =>
    have hP := hwVec_hom (p := p) (q := q) (r := r) (s := s) (leftPositiveIndicator (Sum.inr j₀)) a b c d 0 0 _ 0
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [leftPositiveIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftPositiveIndicator]) _)
      (shapeProd_hom_row _ _ _ j₀ (fun j l => by simp [leftPositiveIndicator, linePos]) _ (posPart_pw c hpc))
      (shapeProd_hom_zero _ _ _ (fun j k => by simp [leftPositiveIndicator, linePos]) _)
    have hN := hwVec_hom (p := p) (q := q) (r := r) (s := s) (leftNegativeIndicator (Sum.inr j₀)) a b c d 0 0 0 _
      (shapeProd_hom_zero _ _ _ (fun i k => by simp [leftNegativeIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun i l => by simp [leftNegativeIndicator]) _)
      (shapeProd_hom_zero _ _ _ (fun j l => by simp [leftNegativeIndicator, linePos]) _)
      (shapeProd_hom_row _ _ _ (Fin.rev j₀) (fun j k => by simp [leftNegativeIndicator, linePos, Fin.rev_eq_iff]) _
        (negPart_pw d hpd))
    refine ⟨((posPart c).getD j₀ 0 : ℤ) - ((negPart d).getD (Fin.rev j₀).val 0 : ℤ), ?_, ?_⟩
    · have hv : (Fin.rev j₀).val = q - 1 - j₀.val := by simp [Fin.val_rev]; omega
      simp only [wtOf1, ofBlocks]
      rw [pad_getD c d q h2 hc hdd j₀.val j₀.isLt, hv]
      push_cast
      ring
    · intro m hm
      rw [monomialLeftWeight_eq_weight_sub, hP hm, hN hm]
      simp
end PI.FJMX
