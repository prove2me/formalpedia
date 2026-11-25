-- Prove2me | solution 1 for PI.WFJM.coeff_fockAct1_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:24:16.893275+00:00
-- url     : https://prove2.me/submissions/8b1b3dd9-c390-4af2-bc4f-bdc2fd640bba

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_omE_self_monomial
import Theorems.Thm_PI_WFJM_fockAct1_Eab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix FockH1Action
namespace PI.WFJM
end PI.WFJM
namespace PI.WFJM
open MvPolynomial
private theorem sgnL_eq_one_of_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = true) : sgnL l = 1 := by
  simp [sgnL, h]
private theorem sgnL_eq_neg_one_of_not_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = false) : sgnL l = -1 := by
  simp [sgnL, h]
open PI.FJM
private theorem sgnL_inl_inl {p q r s : ℕ} (i : Fin p) (k : Fin r) :
    sgnL (p := p) (q := q) (r := r) (s := s) (Sum.inl i, Sum.inl k) = 1 :=
  sgnL_eq_one_of_linePos (by rfl)
private theorem sgnL_inl_inr {p q r s : ℕ} (i : Fin p) (k : Fin s) :
    sgnL (p := p) (q := q) (r := r) (s := s) (Sum.inl i, Sum.inr k) = -1 :=
  sgnL_eq_neg_one_of_not_linePos (by rfl)
private theorem sgnL_inr_inl {p q r s : ℕ} (i : Fin q) (k : Fin r) :
    sgnL (p := p) (q := q) (r := r) (s := s) (Sum.inr i, Sum.inl k) = -1 :=
  sgnL_eq_neg_one_of_not_linePos (by rfl)
private theorem sgnL_inr_inr {p q r s : ℕ} (i : Fin q) (k : Fin s) :
    sgnL (p := p) (q := q) (r := r) (s := s) (Sum.inr i, Sum.inr k) = 1 :=
  sgnL_eq_one_of_linePos (by rfl)
private theorem sgnL_mul_natCast {p q r s : ℕ} (l : FockH1Action.Ln p q r s) (n : ℕ) :
    sgnL l * (n : ℂ) =
      (((if FockH1Action.linePos l then (n : ℤ) else -(n : ℤ)) : ℤ) : ℂ) := by
  cases hl : FockH1Action.linePos l
  · rw [sgnL_eq_neg_one_of_not_linePos hl]
    simp
  · rw [sgnL_eq_one_of_linePos hl]
    simp
private theorem sum_sgnL_right_index_eq_two_mul_sh1 {p q r s : ℕ} (a : FockH1Action.Ix p q) :
    ∑ c : FockH1Action.Ix r s, sgnL (a, c) = ((2 * PI.FJM.sh1 p q r s a : ℚ) : ℂ) := by
  rcases a with i | j <;>
    simp only [Fintype.sum_sum_type, sgnL_inl_inl, sgnL_inl_inr, sgnL_inr_inl,
      sgnL_inr_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      PI.FJM.sh1, Sum.elim_inl, Sum.elim_inr, FockH1Action.cPair] <;>
    push_cast <;> ring
private theorem sum_sgnL_mul_add_half_eq_wt1_add_sh1 {p q r s : ℕ} (a : FockH1Action.Ix p q)
    (m : FockH1Action.Ln p q r s →₀ ℕ) :
    ∑ c : FockH1Action.Ix r s, sgnL (a, c) * (((m (a, c) : ℕ) : ℂ) + 1 / 2) =
      (((PI.FJM.wt1 m a : ℚ) + PI.FJM.sh1 p q r s a : ℚ) : ℂ) := by
  have h1 := sum_sgnL_right_index_eq_two_mul_sh1 (r := r) (s := s) a
  have h2 : ∑ c : FockH1Action.Ix r s, sgnL (a, c) * ((m (a, c) : ℕ) : ℂ) =
      ((PI.FJM.wt1 m a : ℤ) : ℂ) := by
    rw [PI.FJM.wt1, Int.cast_sum]
    exact Finset.sum_congr rfl fun c _ => sgnL_mul_natCast _ _
  have h3 : ∑ c : FockH1Action.Ix r s, sgnL (a, c) * (((m (a, c) : ℕ) : ℂ) + 1 / 2) =
      ∑ c : FockH1Action.Ix r s, sgnL (a, c) * ((m (a, c) : ℕ) : ℂ) +
        (∑ c : FockH1Action.Ix r s, sgnL (a, c)) * (1 / 2) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => mul_add _ _ _
  rw [h3, h2, h1]
  push_cast
  ring
private theorem fockAct1_Eab_diag_monomial {p q r s : ℕ} (a : FockH1Action.Ix p q)
    (m : FockH1Action.Ln p q r s →₀ ℕ) (b : ℂ) :
    FockH1Action.fockAct1 p q r s (FockH1Action.Eab a a) (monomial m b) =
      (((PI.FJM.wt1 m a : ℚ) + PI.FJM.sh1 p q r s a : ℚ) : ℂ) • monomial m b := by
  rw [fockAct1_Eab, LinearMap.sum_apply]
  simp only [omE_self_monomial]
  rw [← Finset.sum_smul, sum_sgnL_mul_add_half_eq_wt1_add_sh1]
section Grade
open MvPolynomial
variable {σ : Type*}
end Grade
section Lap
variable {p q r s : ℕ}
end Lap
section HW
variable {p q r s : ℕ}
open MvPolynomial
end HW
end PI.WFJM
namespace PI.FJM
end PI.FJM
end
end

set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM
variable {p q r s : ℕ}
open MvPolynomial
namespace PI.WFJM
theorem _root_.solution (a : Ix p q) (P : Pol p q r s) (m : Ln p q r s →₀ ℕ) :
    coeff m (fockAct1 p q r s (Eab a a) P) =
      (((wt1 m a : ℚ) + sh1 p q r s a : ℚ) : ℂ) * coeff m P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [fockAct1_Eab_diag_monomial, coeff_smul, smul_eq_mul, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ, mul_add]
end PI.WFJM
