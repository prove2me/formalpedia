-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.homE_norm_coeff_atX_mul_atY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:36:42.186872+00:00
-- url     : https://prove2.me/submissions/0741b7e4-214b-4520-bbb7-102a4c5000fb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_DivByPartialYAtZeroSubstAtXAtY
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
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
variable {lam₁ lam₂ : PowerSeries K} {Φ₁ Φ₂ : MvPowerSeries (Fin 2) K} {A₁ A₂ g : PowerSeries K}
private theorem mvPowerSeries_coeff_subst_X_eq_ite_single {S : Type} [CommRing S] {ι : Type} [DecidableEq ι] (i : ι) (f : PowerSeries S)
    (e : ι →₀ ℕ) :
    MvPowerSeries.coeff e (f.subst (MvPowerSeries.X i : MvPowerSeries ι S)) =
      if e = Finsupp.single i (e i) then coeff (e i) f else 0 := by
  have ha : HasSubst (MvPowerSeries.X i : MvPowerSeries ι S) :=
    HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  rw [PowerSeries.coeff_subst ha]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  split_ifs with h
  · rw [finsum_eq_single _ (e i)]
    · rw [if_pos h]
    · intro d hd
      rw [if_neg]
      intro he
      exact hd (by rw [he, Finsupp.single_eq_same])
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    rw [if_neg]
    intro he
    exact h (by rw [he, Finsupp.single_eq_same])
end ReciprocityTheory.ChartRestriction.L1
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
variable {lam₁ lam₂ : PowerSeries K} {Φ₁ Φ₂ : MvPowerSeries (Fin 2) K} {A₁ A₂ g : PowerSeries K}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {x : K} (a b : PowerSeries K) (ha : IntegralPS a)
    (hb : ‖coeff 1 b‖ ≤ ‖x‖) (n : ℕ) :
    ‖MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 1) (atX a * atY b)‖ ≤ ‖x‖ := by
  unfold IntegralPS at ha
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_induction _ (fun y => ‖y‖ ≤ ‖x‖)
    (fun u v hu hv => (IsUltrametricDist.norm_add_le_max u v).trans (max_le hu hv))
    (by simp) fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  unfold atX atY
  rw [mvPowerSeries_coeff_subst_X_eq_ite_single, mvPowerSeries_coeff_subst_X_eq_ite_single]
  split_ifs with h1 h2
  · have e1 := congrArg (fun f => f 1) hp
    simp only [Finsupp.add_apply] at e1
    rw [h1] at e1
    simp at e1
    rw [norm_mul, e1]
    calc ‖coeff (p.1 0) a‖ * ‖coeff 1 b‖ ≤ 1 * ‖x‖ :=
          mul_le_mul (ha _) hb (norm_nonneg _) zero_le_one
      _ = ‖x‖ := one_mul _
  all_goals simp
end ReciprocityTheory.ChartRestriction.L1
