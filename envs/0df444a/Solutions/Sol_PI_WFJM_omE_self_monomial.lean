-- Prove2me | solution 1 for PI.WFJM.omE_self_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:13:13.816175+00:00
-- url     : https://prove2.me/submissions/d3fbca78-3337-4a99-866a-780d3e0715d6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_X_mul_pderiv_monomial
import Theorems.Thm_PI_WFJM_pderiv_X_mul_monomial
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
private theorem pderiv_toLinearMap_apply {σ : Type*} (i : σ) (P : MvPolynomial σ ℂ) :
    (pderiv i).toLinearMap P = pderiv i P := rfl
private theorem moduleEnd_mul_apply {M : Type*} [AddCommGroup M] [Module ℂ M]
    (f g : Module.End ℂ M) (x : M) : (f * g) x = f (g x) := rfl
private theorem moduleEnd_one_apply {M : Type*} [AddCommGroup M] [Module ℂ M] (x : M) :
    (1 : Module.End ℂ M) x = x := rfl
private theorem sgnL_eq_one_of_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = true) : sgnL l = 1 := by
  simp [sgnL, h]
private theorem sgnL_eq_neg_one_of_not_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = false) : sgnL l = -1 := by
  simp [sgnL, h]
private theorem raiB_eq_mulLeft_X_of_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = true) : FockH1Action.raiB l = LinearMap.mulLeft ℂ (X l) := by
  rw [FockH1Action.raiB, if_pos h]
private theorem raiB_eq_neg_pderiv_of_not_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = false) : FockH1Action.raiB l = -(pderiv l).toLinearMap := by
  rw [FockH1Action.raiB, if_neg (show ¬ (FockH1Action.linePos l = true) by simp [h])]
private theorem lowB_eq_pderiv_of_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = true) : FockH1Action.lowB l = (pderiv l).toLinearMap := by
  rw [FockH1Action.lowB, if_pos h]
private theorem lowB_eq_mulLeft_X_of_not_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = false) : FockH1Action.lowB l = LinearMap.mulLeft ℂ (X l) := by
  rw [FockH1Action.lowB, if_neg (show ¬ (FockH1Action.linePos l = true) by simp [h])]
open PI.FJM
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
namespace PI.WFJM
theorem _root_.solution {p q r s : ℕ} (l : Ln p q r s) (α : Ln p q r s →₀ ℕ) (c : ℂ) :
    omE l l (monomial α c) = (sgnL l * (((α l : ℕ) : ℂ) + 1 / 2)) • monomial α c := by
  have h1 := X_mul_pderiv_monomial l α c
  have h2 := pderiv_X_mul_monomial l α c
  rw [FockH1Action.omE, if_pos rfl, LinearMap.add_apply, moduleEnd_mul_apply, LinearMap.smul_apply,
    moduleEnd_one_apply]
  cases hl : FockH1Action.linePos l
  · rw [raiB_eq_neg_pderiv_of_not_linePos hl, lowB_eq_mulLeft_X_of_not_linePos hl, sgnL_eq_neg_one_of_not_linePos hl, LinearMap.neg_apply,
      LinearMap.mulLeft_apply, pderiv_toLinearMap_apply, h2]
    first
    | module
    | (rw [← neg_smul, ← add_smul]; congr 1; ring)
  · rw [raiB_eq_mulLeft_X_of_linePos hl, lowB_eq_pderiv_of_linePos hl, sgnL_eq_one_of_linePos hl, pderiv_toLinearMap_apply,
      LinearMap.mulLeft_apply, h1]
    first
    | module
    | (rw [← add_smul]; congr 1; ring)
end PI.WFJM
