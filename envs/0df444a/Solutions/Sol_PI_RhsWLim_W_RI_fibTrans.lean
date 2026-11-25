-- Prove2me | solution 1 for PI.RhsWLim.W.RI.fibTrans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:27:52.38789+00:00
-- url     : https://prove2.me/submissions/22e46761-46ec-4458-807b-5682cbfd4339

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvF
import Theorems.Thm_PI_RhsWLim_W_RI_herm_add_left
import Theorems.Thm_PI_RhsWLim_W_RI_herm_sub_left
import Theorems.Thm_PI_RhsWLim_W_RI_herm_smul_left
import Theorems.Thm_PI_RhsWLim_W_RI_herm_add_right
import Theorems.Thm_PI_RhsWLim_W_RI_herm_sub_right
import Theorems.Thm_PI_RhsWLim_W_RI_herm_smul_right
import Theorems.Thm_PI_RhsWLim_W_RI_herm_symm
import Theorems.Thm_PI_RhsWLim_W_RI_unit_of_form
import Theorems.Thm_PI_RhsWLim_W_RI_tmat_mulVec
import Theorems.Thm_PI_RhsWLim_W_RI_wb_posdef
import Theorems.Thm_PI_RhsWLim_W_RI_herm_e_wb
import Theorems.Thm_PI_RhsWLim_W_RI_uwset_one
import Theorems.Thm_PI_RhsWLim_W_MB_hpk_herm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ}
namespace PI.RhsWLim.W.RI
theorem _root_.solution : FibTrans := by
  intro k r z v v' hz hv hv' hT h1 h2
  by_cases hvv : v = v'
  · exact ⟨1, uwset_one z, by rw [hvv, Matrix.one_mulVec]⟩
  have hsym := herm_symm (Hpk k r) MB.hpk_herm
  set d := v - v' with hddef
  have hd : inWb k r d := fun i hi => by simp only [hddef, Pi.sub_apply, hv i hi, hv' i hi, sub_zero]
  have hdz : herm (Hpk k r) d z = 0 := by rw [herm_sub_left, h2, sub_self]
  have hN : herm (Hpk k r) d d = herm (Hpk k r) v d + star (herm (Hpk k r) v d) := by
    simp only [hddef, herm_sub_left, herm_sub_right, star_sub]
    rw [← hsym v v, ← hsym v v', ← h1]
    ring
  have hne : herm (Hpk k r) v d ≠ 0 := by
    intro h0
    have : herm (Hpk k r) d d = 0 := by rw [hN, h0, star_zero, add_zero]
    exact hvv (sub_eq_zero.1 (wb_posdef hz hT hd hdz this))
  have hne' : star (herm (Hpk k r) v d) ≠ 0 := star_ne_zero.2 hne
  set κ : ℂ := -(herm (Hpk k r) v d)⁻¹ with hκ
  have hTx := tmat_mulVec (Hpk k r) κ d
  have hfix : ∀ x, herm (Hpk k r) x d = 0 → tmat (Hpk k r) κ d *ᵥ x = x := by
    intro x hx
    rw [hTx, hx, mul_zero, zero_smul, add_zero]
  have hbr : κ + star κ + κ * star κ * herm (Hpk k r) d d = 0 := by
    rw [hN, hκ, star_neg, star_inv₀]
    field_simp
    ring
  have hunit : ∀ x w, herm (Hpk k r) (tmat (Hpk k r) κ d *ᵥ x) (tmat (Hpk k r) κ d *ᵥ w) = herm (Hpk k r) x w := by
    intro x w
    rw [hTx, hTx, herm_add_left, herm_add_right, herm_add_right, herm_smul_left, herm_smul_left,
      herm_smul_right, herm_smul_right, hsym w d, star_mul']
    linear_combination (herm (Hpk k r) x d * star (herm (Hpk k r) w d)) * hbr
  have hzd : herm (Hpk k r) z d = 0 := by rw [hsym d z, hdz, star_zero]
  refine ⟨tmat (Hpk k r) κ d, ⟨unit_of_form _ _ hunit, fun a => ⟨hfix _ (herm_e_wb hd ?_), hfix _ (herm_e_wb hd ?_)⟩,
    hfix z hzd⟩, ?_⟩
  · left
    exact a.isLt
  · right
    show r + k < 2 * r + k - a.val
    omega
  · rw [hTx, hκ, neg_mul, inv_mul_cancel₀ hne, neg_one_smul, hddef]
    abel
end PI.RhsWLim.W.RI
