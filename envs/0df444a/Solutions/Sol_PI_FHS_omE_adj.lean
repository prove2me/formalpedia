-- Prove2me | solution 1 for PI.FHS.omE_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:23.174401+00:00
-- url     : https://prove2.me/submissions/f1c80ec1-74bc-4ebf-aa6a-fb15d01a2e8c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker
import Theorems.Thm_PI_FHS_omE_apply_of_ne
import Theorems.Thm_PI_FHS_fockInner_X_mul
import Theorems.Thm_PI_FHS_fockInner_neg_left
import Theorems.Thm_PI_FHS_fockInner_neg_right
import Theorems.Thm_PI_FHS_fockInner_pderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial Matrix FockH1Action
namespace PI.FHS
section Sums
variable {σ : Type*}
end Sums
variable {p q r s : ℕ}
private theorem raiB_apply_eq_X_mul_of_linePos {m : FockH1Action.Ln p q r s} (h : FockH1Action.linePos m = true)
    (P : FockH1Action.Pol p q r s) : FockH1Action.raiB m P = X m * P := by
  rw [FockH1Action.raiB, if_pos h]; rfl
private theorem raiB_apply_eq_neg_pderiv_of_not_linePos {m : FockH1Action.Ln p q r s} (h : FockH1Action.linePos m = false)
    (P : FockH1Action.Pol p q r s) : FockH1Action.raiB m P = -(pderiv m P) := by
  rw [FockH1Action.raiB, if_neg (by simp [h])]; rfl
private theorem lowB_apply_eq_pderiv_of_linePos {m : FockH1Action.Ln p q r s} (h : FockH1Action.linePos m = true)
    (P : FockH1Action.Pol p q r s) : FockH1Action.lowB m P = pderiv m P := by
  rw [FockH1Action.lowB, if_pos h]; rfl
private theorem lowB_apply_eq_X_mul_of_not_linePos {m : FockH1Action.Ln p q r s} (h : FockH1Action.linePos m = false)
    (P : FockH1Action.Pol p q r s) : FockH1Action.lowB m P = X m * P := by
  rw [FockH1Action.lowB, if_neg (by simp [h])]; rfl
end PI.FHS
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix FockH1Action
open PI PI.FHS
variable {p q r s : ℕ}
namespace PI.FHS
theorem _root_.solution {l l' : Ln p q r s} (h : linePos l ≠ linePos l') (P Q : Pol p q r s) :
    fockInner (omE l l' P) Q = - fockInner P (omE l' l Q) := by
  have hne : l ≠ l' := fun e => h (e ▸ rfl)
  rw [omE_apply_of_ne hne, omE_apply_of_ne (Ne.symm hne)]
  cases hl : FockH1Action.linePos l <;> cases hl' : FockH1Action.linePos l'
  · exact absurd (hl.trans hl'.symm) h
  · rw [lowB_apply_eq_pderiv_of_linePos hl', raiB_apply_eq_neg_pderiv_of_not_linePos hl, lowB_apply_eq_X_mul_of_not_linePos hl, raiB_apply_eq_X_mul_of_linePos hl',
      fockInner_neg_left, fockInner_pderiv, fockInner_pderiv]
  · rw [lowB_apply_eq_X_mul_of_not_linePos hl', raiB_apply_eq_X_mul_of_linePos hl, lowB_apply_eq_pderiv_of_linePos hl, raiB_apply_eq_neg_pderiv_of_not_linePos hl',
      fockInner_neg_right, neg_neg, fockInner_X_mul, fockInner_X_mul]
  · exact absurd (hl.trans hl'.symm) h
end PI.FHS
