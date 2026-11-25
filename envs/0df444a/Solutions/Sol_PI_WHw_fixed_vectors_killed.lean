-- Prove2me | solution 1 for PI.WHw.fixed_vectors_killed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:15.406369+00:00
-- url     : https://prove2.me/submissions/186581a2-1a8d-448f-b99e-3956626e3469

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionA
import Theorems.Thm_PI_WHw_coeff_mem_of_eval
import Theorems.Thm_PI_WHw_eval_rowGen
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
private theorem transpose_one_add_single {N : ℕ} (a b : Fin N) (c : ℂ) :
    (1 + Matrix.single a b c).transpose = 1 + Matrix.single b a c := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, ite_and]
  split_ifs <;> subst_vars <;> simp_all
end PI.WHw
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WHw
theorem _root_.solution : FixedKilledC := by
  intro N lam f _hf hfix a b hab k hk
  have hne : a ≠ b := ne_of_lt hab
  have key : ∀ m : ℕ, (rowGen ℂ a b f - Polynomial.C f).eval (C (m : ℂ)) ∈
      (⊥ : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ)) := by
    intro m
    rw [Submodule.mem_bot, Polynomial.eval_sub, Polynomial.eval_C, eval_rowGen, sub_eq_zero]
    have hdet : (1 + Matrix.single a b (m : ℂ)).det = 1 := Matrix.det_transvection_of_ne a b hne _
    have hu : IsUnit (1 + Matrix.single a b (m : ℂ)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hdet]; exact isUnit_one)
    have h1 := hfix hu.unit ?_ ?_
    · unfold Formalism.BasicNotions.sqAct at h1
      rw [hu.unit_spec, transpose_one_add_single] at h1
      have hd1 : Formalism.BasicNotions.detPow ℂ N hu.unit lam.detShift = 1 := by
        unfold Formalism.BasicNotions.detPow
        have h3 : Matrix.GeneralLinearGroup.det hu.unit = 1 := by
          apply Units.ext
          rw [Matrix.GeneralLinearGroup.val_det_apply, hu.unit_spec, hdet, Units.val_one]
        rw [h3, one_zpow, Units.val_one]
      rw [hd1, one_smul] at h1
      exact h1
    · intro i j hji
      rw [hu.unit_spec, Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hji).symm, zero_add]
      simp only [Matrix.single_apply]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        exact absurd (hab.trans hji) (lt_irrefl _)
      · rfl
    · intro i
      rw [hu.unit_spec, Matrix.add_apply, Matrix.one_apply_eq]
      simp only [Matrix.single_apply]
      split_ifs with h
      · exact absurd (h.1.trans h.2.symm) hne
      · simp
  have h4 := coeff_mem_of_eval ⊥ _ key k
  rw [Submodule.mem_bot, Polynomial.coeff_sub, Polynomial.coeff_C, if_neg (by omega), sub_zero] at h4
  exact h4
end PI.WHw
