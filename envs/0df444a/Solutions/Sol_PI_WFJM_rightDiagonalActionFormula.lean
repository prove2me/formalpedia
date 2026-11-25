-- Prove2me | solution 1 for PI.WFJM.rightDiagonalActionFormula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:23:35.605379+00:00
-- url     : https://prove2.me/submissions/e5ac0ded-93a0-4974-af4b-2422b39816ae

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_omE_self_monomial
import Theorems.Thm_PI_WFJM_fockAct2_Eab
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
private theorem sum_sgnL_left_index_eq_two_mul_sh2 {p q r s : ℕ} (c : FockH1Action.Ix r s) :
    ∑ a : FockH1Action.Ix p q, sgnL (a, c) = ((2 * PI.FJM.sh2 p q r s c : ℚ) : ℂ) := by
  rcases c with k | l <;>
    simp only [Fintype.sum_sum_type, sgnL_inl_inl, sgnL_inl_inr, sgnL_inr_inl,
      sgnL_inr_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      PI.FJM.sh2, Sum.elim_inl, Sum.elim_inr, FockH1Action.cPair] <;>
    push_cast <;> ring
private theorem sum_sgnL_mul_add_half_eq_wt2_add_sh2 {p q r s : ℕ} (c : FockH1Action.Ix r s)
    (m : FockH1Action.Ln p q r s →₀ ℕ) :
    ∑ a : FockH1Action.Ix p q, sgnL (a, c) * (((m (a, c) : ℕ) : ℂ) + 1 / 2) =
      (((PI.FJM.wt2 m c : ℚ) + PI.FJM.sh2 p q r s c : ℚ) : ℂ) := by
  have h1 := sum_sgnL_left_index_eq_two_mul_sh2 (p := p) (q := q) c
  have h2 : ∑ a : FockH1Action.Ix p q, sgnL (a, c) * ((m (a, c) : ℕ) : ℂ) =
      ((PI.FJM.wt2 m c : ℤ) : ℂ) := by
    rw [PI.FJM.wt2, Int.cast_sum]
    exact Finset.sum_congr rfl fun a _ => sgnL_mul_natCast _ _
  have h3 : ∑ a : FockH1Action.Ix p q, sgnL (a, c) * (((m (a, c) : ℕ) : ℂ) + 1 / 2) =
      ∑ a : FockH1Action.Ix p q, sgnL (a, c) * ((m (a, c) : ℕ) : ℂ) +
        (∑ a : FockH1Action.Ix p q, sgnL (a, c)) * (1 / 2) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => mul_add _ _ _
  rw [h3, h2, h1]
  push_cast
  ring
private theorem fockAct2_Eab_diag_monomial {p q r s : ℕ} (c : FockH1Action.Ix r s)
    (m : FockH1Action.Ln p q r s →₀ ℕ) (b : ℂ) :
    FockH1Action.fockAct2 p q r s (FockH1Action.Eab c c) (monomial m b) =
      (((PI.FJM.wt2 m c : ℚ) + PI.FJM.sh2 p q r s c : ℚ) : ℂ) • monomial m b := by
  rw [fockAct2_Eab, LinearMap.sum_apply]
  simp only [omE_self_monomial]
  rw [← Finset.sum_smul, sum_sgnL_mul_add_half_eq_wt2_add_sh2]
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
namespace PI.WFJM
theorem _root_.solution : FormWt2 := by
  intro p q r s c m
  exact fockAct2_Eab_diag_monomial c m 1
end PI.WFJM
