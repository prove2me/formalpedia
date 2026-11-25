-- Prove2me | solution 1 for PI.WeylForKWork.dominant_restriction_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:55.696256+00:00
-- url     : https://prove2.me/submissions/7f9d6fe3-181d-4076-b2ba-fdbe8bf4cdf0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Formula
import Theorems.Thm_PI_WeylForKWork_eps_ePl
import Theorems.Thm_PI_WeylForKWork_eps_eMi
import Theorems.Thm_PI_WeylForKWork_ePl_lt_iff
import Theorems.Thm_PI_WeylForKWork_eMi_lt_iff
import Theorems.Thm_PI_WeylForKWork_ePl_inj
import Theorems.Thm_PI_WeylForKWork_eMi_inj
import Theorems.Thm_PI_WeylForKWork_ePl_ne_eMi
import Theorems.Thm_PI_WeylForKWork_prod_split
import Theorems.Thm_PI_WeylForKWork_eMi_ne_ePl
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix Finset
variable {N : ℕ}
namespace PI.WeylForKWork
theorem _root_.solution : CDomRes := by
  have sum_split {N : ℕ} {M : Type} [AddCommMonoid M] (ε : Fin N → Bool) (f : Fin N → M) :
      ∑ a, f a = (∑ i, f (ePl ε i)) + ∑ j, f (eMi ε j) := by
    rw [← Equiv.sum_comp (blk ε), Fintype.sum_sum_type]
    rfl
  intro N ε μ Λ hCD
  obtain ⟨c, hc, hsum⟩ := hCD
  constructor
  · refine ⟨fun i j => c (ePl ε i) (ePl ε j),
      fun i j h => ⟨(ePl_lt_iff ε i j).1 (hc _ _ h).1, rfl⟩, ?_⟩
    funext k
    have hk := congr_fun hsum (ePl ε k)
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    have hT0 : ∀ j b, (c (eMi ε j) b : ℝ) * root (eMi ε j) b (ePl ε k) = 0 := by
      intro j b
      by_cases h0 : c (eMi ε j) b = 0
      · simp [h0]
      · have he := (hc _ _ h0).2
        rw [eps_eMi ε j] at he
        have hb : b ≠ ePl ε k := by
          rintro rfl
          rw [eps_ePl ε k] at he
          exact absurd he (by decide)
        have ha : ePl ε k ≠ eMi ε j := ePl_ne_eMi ε k j
        simp [root, Pi.single_apply, ha, hb.symm]
    have hT1 : ∀ i j, (c (ePl ε i) (eMi ε j) : ℝ) = 0 := by
      intro i j
      by_contra h0
      have he := (hc _ _ (by exact_mod_cast h0)).2
      rw [eps_ePl ε i, eps_eMi ε j] at he
      exact absurd he (by decide)
    rw [hk, sum_split ε]
    simp only [hT0, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_split ε]
    simp only [hT1, zero_mul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp [root, Pi.single_apply, ePl_inj]
  · refine ⟨fun i j => c (eMi ε i) (eMi ε j),
      fun i j h => ⟨(eMi_lt_iff ε i j).1 (hc _ _ h).1, rfl⟩, ?_⟩
    funext k
    have hk := congr_fun hsum (eMi ε k)
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢
    have hT0 : ∀ j b, (c (ePl ε j) b : ℝ) * root (ePl ε j) b (eMi ε k) = 0 := by
      intro j b
      by_cases h0 : c (ePl ε j) b = 0
      · simp [h0]
      · have he := (hc _ _ h0).2
        rw [eps_ePl ε j] at he
        have hb : b ≠ eMi ε k := by
          rintro rfl
          rw [eps_eMi ε k] at he
          exact absurd he (by decide)
        have ha : eMi ε k ≠ ePl ε j := eMi_ne_ePl ε k j
        simp [root, Pi.single_apply, ha, hb.symm]
    have hT1 : ∀ i j, (c (eMi ε i) (ePl ε j) : ℝ) = 0 := by
      intro i j
      by_contra h0
      have he := (hc _ _ (by exact_mod_cast h0)).2
      rw [eps_eMi ε i, eps_ePl ε j] at he
      exact absurd he (by decide)
    rw [hk, sum_split ε]
    simp only [hT0, Finset.sum_const_zero, zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_split ε]
    simp only [hT1, zero_mul, Finset.sum_const_zero, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp [root, Pi.single_apply, eMi_inj]
end PI.WeylForKWork
