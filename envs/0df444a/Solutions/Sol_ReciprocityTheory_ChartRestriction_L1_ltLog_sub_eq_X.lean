-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.ltLog_sub_eq_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:45:16.233165+00:00
-- url     : https://prove2.me/submissions/0c8102dc-8451-4b20-a4ae-ed8ea36638de

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SemilinNormPowSubPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgFinA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
omit [IsUltrametricDist K] [CharZero K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (hl : 2 ≤ l) (τ : K →+* K) :
    ltLog K l - (l : K)⁻¹ • (PowerSeries.map τ (ltLog K l)).subst ((X : PowerSeries K) ^ (l ^ 2))
      = X := by
  have hq : 2 ≤ l ^ 2 := by nlinarith
  have hq0 : l ^ 2 ≠ 0 := by omega
  have hsub : ∀ (f : PowerSeries K) {k : ℕ} (_ : k ≠ 0) (m : ℕ),
      coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
    intro f k hk m
    have ha : PowerSeries.HasSubst ((X : PowerSeries K) ^ k) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hk])
    rw [PowerSeries.coeff_subst' ha]
    simp only [← pow_mul, PowerSeries.coeff_X_pow]
    split_ifs with hd
    · obtain ⟨q, rfl⟩ := hd
      rw [finsum_eq_single _ q]
      · simp [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hk)]
      · intro d hd
        have : k * q ≠ k * d := fun h => hd (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h).symm
        simp [this]
    · rw [finsum_eq_zero_of_forall_eq_zero]
      intro d
      have : m ≠ k * d := fun h => hd ⟨d, h⟩
      simp [this]
  have hpow : ∀ j, coeff ((l ^ 2) ^ j) (ltLog K l) = ((l : K) ^ j)⁻¹ := by
    intro j
    have hex : ∃ i : ℕ, (l ^ 2) ^ j = (l ^ 2) ^ i := ⟨j, rfl⟩
    rw [Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk, dif_pos hex]
    have hf : Nat.find hex = j := (Nat.pow_right_injective hq (Nat.find_spec hex)).symm
    rw [hf]
  ext n
  rw [map_sub, PowerSeries.coeff_smul, hsub _ hq0, PowerSeries.coeff_X]
  by_cases hn : ∃ j, n = (l ^ 2) ^ j
  · obtain ⟨j, rfl⟩ := hn
    rcases j with _ | j
    · have h1 : (l ^ 2) ^ 0 = 1 := pow_zero _
      have hnd : ¬ l ^ 2 ∣ (l ^ 2) ^ 0 := by
        rw [h1]
        intro h
        have := Nat.le_of_dvd one_pos h
        omega
      rw [if_neg hnd, hpow 0, h1, if_pos rfl]
      simp
    · have hd : l ^ 2 ∣ (l ^ 2) ^ (j + 1) := dvd_pow_self _ (Nat.succ_ne_zero j)
      have hdiv : (l ^ 2) ^ (j + 1) / l ^ 2 = (l ^ 2) ^ j := by
        rw [pow_succ (l ^ 2) j, Nat.mul_div_cancel _ (by omega)]
      have hne : (l ^ 2) ^ (j + 1) ≠ 1 := by
        have : l ^ 2 ≤ (l ^ 2) ^ (j + 1) := Nat.le_self_pow (Nat.succ_ne_zero j) _
        omega
      rw [if_pos hd, hdiv, PowerSeries.coeff_map, hpow, hpow,
        if_neg hne, map_inv₀, map_pow, map_natCast, pow_succ (l : K) j, mul_inv]
      ring
  · have h0 : coeff n (ltLog K l) = 0 := by rw [Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk, dif_neg hn]
    have hX : n ≠ 1 := fun h => hn ⟨0, by rw [h, pow_zero]⟩
    rw [h0, if_neg hX]
    split_ifs with hd
    · obtain ⟨m, rfl⟩ := hd
      have hm : ¬ ∃ j, m = (l ^ 2) ^ j := fun ⟨j, hj⟩ => hn ⟨j + 1, by rw [hj, pow_succ (l ^ 2) j, mul_comm]⟩
      rw [Nat.mul_div_cancel_left m (by omega), PowerSeries.coeff_map, Formalism.L2.Th1.CM.ltLog, PowerSeries.coeff_mk,
        dif_neg hm, map_zero]
      simp
    · simp
end ReciprocityTheory.ChartRestriction.L1
