-- Prove2me | solution 1 for PI.PhiCubeOfFactor.Wk.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:52.281438+00:00
-- url     : https://prove2.me/submissions/e85b3034-37a5-4777-a460-4264c33e18f6

import Definitions.Def_Formalism_PeriodIntegrals_PhiCubeOfFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_CoeffSingleLg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialFactorIdentity_ExpMvEq
import Theorems.Thm_PI_PhiCubeOfFactor_Wk_logMv_eq
import Theorems.Thm_PI_PhiCubeOfFactor_Wk_expMv_eq
import Theorems.Thm_P2M_PI_FglShared_expMv_add__f0eb8b5a05d0
import Theorems.Thm_P2M_PI_FglShared_expMv_subst__fa51dcff15ff
import Theorems.Thm_PI_FglShared_coeff_single_lg
import Theorems.Thm_PI_FglShared_constantCoeff_logS
import Theorems.Thm_PI_FglShared_constantCoeff_subst_of_zero
import Theorems.Thm_PI_FglShared_exists_coeff_ne
import Theorems.Thm_PI_FglShared_expMv_logS
import Theorems.Thm_PI_FglShared_int_of_mul_eq_one
import Theorems.Thm_PI_FglShared_l_constantCoeff
import Theorems.Thm_PI_FglShared_subst_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PhiCubeOfFactor PI.PhiCubeOfFactor.Wk
open PI.PhiCubeOfFactor MvPowerSeries PI.FglShared
variable {p : ℕ} [Fact p.Prime]
namespace PI.PhiCubeOfFactor.Wk
theorem _root_.solution : Lemma := by
  intro p _ l ex E Q hex0 hinv hE1 hfun hQ
  obtain ⟨n, hnI, hn0, rfl⟩ := hQ
  have hl0 := l_constantCoeff hex0 hinv
  have hcX : ∀ i : Fin 2, constantCoeff (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    fun i => constantCoeff_X i
  have hlg : ∀ i : Fin 2, constantCoeff (lg l (Xv i : MvPowerSeries (Fin 2) ℂ_[p])) = 0 := by
    intro i
    unfold lg
    rw [constantCoeff_subst_of_zero (hcX i)]
    exact hl0
  have hs0 : constantCoeff (lg l (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) + lg l (Xv 1)) = 0 := by
    rw [map_add, hlg, hlg, add_zero]
  have hd0 : constantCoeff (lg l (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) - lg l (Xv 1)) = 0 := by
    rw [map_sub, hlg, hlg, sub_zero]
  have hA0 : constantCoeff (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    unfold add pt
    rw [constantCoeff_subst_of_zero hs0]
    exact hex0
  have hB0 : constantCoeff (sub l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    unfold sub pt
    rw [constantCoeff_subst_of_zero hd0]
    exact hex0
  obtain ⟨k, hk, hlk⟩ := exists_coeff_ne hex0 hinv
  have hc0 : ∀ i : Fin 2, coeff (Finsupp.single (0 : Fin 2) k) (lg l (Xv i : MvPowerSeries (Fin 2) ℂ_[p])) =
      if i = 0 then PowerSeries.coeff k l else 0 := fun i => coeff_single_lg l 0 i hk
  have hAne : (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    unfold add pt
    refine subst_ne_zero hex0 hinv hs0 ?_
    intro h
    have h2 := congrArg (coeff (Finsupp.single (0 : Fin 2) k)) h
    rw [map_add, map_zero, hc0, hc0] at h2
    simp at h2
    exact hlk h2
  have hBne : (sub l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    unfold sub pt
    refine subst_ne_zero hex0 hinv hd0 ?_
    intro h
    have h2 := congrArg (coeff (Finsupp.single (0 : Fin 2) k)) h
    rw [map_sub, map_zero, hc0, hc0] at h2
    simp at h2
    exact hlk h2
  have hcanc : eAt E (add l ex (Xv 0) (Xv 1)) * eAt E (sub l ex (Xv 0) (Xv 1)) =
      n * eAt E (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 * eAt E (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 := by
    apply mul_left_cancel₀ (mul_ne_zero hAne hBne)
    linear_combination hfun
  have hexp0 : PI.FglPhSplit.expMv (0 : PowerSeries ℂ_[p]) = 1 := by
    refine MvPowerSeries.ext fun α => ?_
    change (∑ m ∈ Finset.range ((α.sum fun _ k => k) + 1),
      MvPowerSeries.coeff α ((0 : PowerSeries ℂ_[p]) ^ m) / (m.factorial : ℂ_[p])) = MvPowerSeries.coeff α 1
    rw [Finset.sum_eq_single 0 (fun m _ hm => by rw [zero_pow hm, map_zero, zero_div])
      (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h)]
    simp
  have hL0 : constantCoeff (logS E) = 0 := constantCoeff_logS E
  have hnL0 : constantCoeff (-logS E) = 0 := by rw [map_neg, hL0, neg_zero]
  have hUE : PI.FglPhSplit.expMv (-logS E) * E = 1 := by
    have h := expMv_add' hnL0 hL0
    rw [neg_add_cancel, hexp0, expMv_logS hE1] at h
    exact h.symm
  have hsub : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff a = 0 →
      PI.FglPhSplit.expMv (phAt E a) * eAt E a = 1 := by
    intro a ha
    have hS : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
    unfold phAt eAt
    rw [logMv_eq, expMv_subst' ha hnL0, ← PowerSeries.subst_mul hS, hUE, ← PowerSeries.coe_substAlgHom hS,
      map_one]
  have hneg : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff a = 0 →
      PI.FglPhSplit.expMv (-phAt E a) = eAt E a := by
    intro a ha
    have hS : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
    unfold phAt eAt
    rw [logMv_eq, ← PowerSeries.coe_substAlgHom hS, ← map_neg, neg_neg, PowerSeries.coe_substAlgHom hS,
      expMv_subst' ha hL0, expMv_logS hE1]
  have hph0 : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff a = 0 → constantCoeff (phAt E a) = 0 := by
    intro a ha
    unfold phAt
    rw [constantCoeff_subst_of_zero ha, logMv_eq]
    exact hnL0
  have hnph0 : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff a = 0 → constantCoeff (-phAt E a) = 0 := by
    intro a ha
    rw [map_neg, hph0 a ha, neg_zero]
  have hf : phAt E (add l ex (Xv 0) (Xv 1)) + phAt E (sub l ex (Xv 0) (Xv 1)) -
      (2 * phAt E (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) + 2 * phAt E (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p])) =
      phAt E (add l ex (Xv 0) (Xv 1)) + phAt E (sub l ex (Xv 0) (Xv 1)) + -phAt E (Xv 0) + -phAt E (Xv 0) +
        -phAt E (Xv 1) + -phAt E (Xv 1) := by ring
  refine ⟨?_, ?_⟩
  · rw [hf, map_add, map_add, map_add, map_add, map_add, hph0 _ hA0, hph0 _ hB0, hnph0 _ (hcX 0),
      hnph0 _ (hcX 1)]
    ring
  · rw [expMv_eq, hf]
    have c1 := hph0 _ hA0
    have c2 := hph0 _ hB0
    have c3 := hnph0 _ (hcX 0)
    have c4 := hnph0 _ (hcX 1)
    rw [expMv_add' (by simp only [map_add, c1, c2, c3, c4, add_zero]) c4,
      expMv_add' (by simp only [map_add, c1, c2, c3, add_zero]) c4,
      expMv_add' (by simp only [map_add, c1, c2, c3, add_zero]) c3,
      expMv_add' (by simp only [map_add, c1, c2, add_zero]) c3,
      expMv_add' c1 c2, hneg _ (hcX 0), hneg _ (hcX 1)]
    refine int_of_mul_eq_one hnI hn0 ?_
    have e1 := hsub _ hA0
    have e2 := hsub _ hB0
    linear_combination (PI.FglPhSplit.expMv (phAt E (add l ex (Xv 0) (Xv 1))) *
      PI.FglPhSplit.expMv (phAt E (sub l ex (Xv 0) (Xv 1)))) * hcanc.symm +
      PI.FglPhSplit.expMv (phAt E (sub l ex (Xv 0) (Xv 1))) * eAt E (sub l ex (Xv 0) (Xv 1)) * e1 + e2
end PI.PhiCubeOfFactor.Wk
