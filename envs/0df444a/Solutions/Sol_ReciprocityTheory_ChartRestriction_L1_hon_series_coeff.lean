-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.hon_series_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:37:50.720961+00:00
-- url     : https://prove2.me/submissions/9bf69516-8e61-4115-8566-e48a94a98105

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hon_lt_sq_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
section Regroup
variable {K : Type} [Field K]
end Regroup
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] {l : ℕ}
  {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}
private theorem coeff_subst_X_pow_eq_ite_dvd' (f : PowerSeries K) {k : ℕ} (hk : k ≠ 0) (m : ℕ) :
    coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
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
end ReciprocityTheory.ChartRestriction.L1
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] {l : ℕ}
  {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (hl : 2 ≤ l) (τ : K →+* K) (c : ℕ → K)
    (h : ∀ N : ℕ, ∃ R : PowerSeries K, constantCoeff R = 0 ∧
      DivBy (l : K) (C (l : K) * lam
        - ∑ i ∈ Finset.range N, C (c i) *
            (PowerSeries.map (τ ^ (i + 1)) lam).subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (i + 1)))
        - R.subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (N + 1))))) (n : ℕ) :
    ‖(l : K) * coeff n lam - ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)‖ ≤ ‖(l : K)‖ := by
  obtain ⟨R, hR0, hR⟩ := h n
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  have hRn : coeff n (R.subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (n + 1)))) = 0 := by
    rw [coeff_subst_X_pow_eq_ite_dvd' R (pow_ne_zero _ hq)]
    split_ifs
    · rw [Nat.div_eq_of_lt (lt_of_lt_of_le (hon_lt_sq_pow hl n)
          (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hq) (Nat.le_succ n))),
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hR0]
    · rfl
  have hsum : coeff n (∑ i ∈ Finset.range n, C (c i) *
        (PowerSeries.map (τ ^ (i + 1)) lam).subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (i + 1))))
      = ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
          c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam) := by
    rw [map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerSeries.coeff_C_mul, coeff_subst_X_pow_eq_ite_dvd' _ (pow_ne_zero _ hq)]
    split_ifs
    · rw [PowerSeries.coeff_map]
    · rw [mul_zero]
  unfold DivBy at hR
  have hcoef := hR n
  rw [map_sub, map_sub, PowerSeries.coeff_C_mul, hsum, hRn, sub_zero] at hcoef
  exact hcoef
end ReciprocityTheory.ChartRestriction.L1
