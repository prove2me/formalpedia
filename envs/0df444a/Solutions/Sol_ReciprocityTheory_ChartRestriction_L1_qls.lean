-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.qls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:55:56.594976+00:00
-- url     : https://prove2.me/submissions/2f1cf09a-8d39-40ec-943e-583c40b68ffa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonA
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
private theorem norm_finsum_le_of_forall_norm_le_univ_sort {α : Type*} (f : α → K) {C : ℝ} (hC : 0 ≤ C) (h : ∀ a, ‖f a‖ ≤ C) :
    ‖∑ᶠ a, f a‖ ≤ C := by
  classical
  rw [finsum_def]
  split_ifs with hs
  · exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun i _ => h i
  · simpa using hC
private theorem mvPowerSeries_norm_coeff_mul_le_mul {ι : Type} {F G : MvPowerSeries ι K} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hF : ∀ e, ‖MvPowerSeries.coeff e F‖ ≤ a) (hG : ∀ e, ‖MvPowerSeries.coeff e G‖ ≤ b) :
    ∀ e, ‖MvPowerSeries.coeff e (F * G)‖ ≤ a * b := by
  classical
  intro e
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun p _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hF _) (hG _) (norm_nonneg _) ha
private theorem mvPowerSeries_norm_coeff_pow_le_pow {ι : Type} {F : MvPowerSeries ι K} {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ e, ‖MvPowerSeries.coeff e F‖ ≤ c) :
    ∀ (m : ℕ) (e : ι →₀ ℕ), ‖MvPowerSeries.coeff e (F ^ m)‖ ≤ c ^ m := by
  classical
  intro m
  induction m with
  | zero =>
    intro e
    rw [pow_zero, pow_zero, MvPowerSeries.coeff_one]
    split_ifs <;> simp
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact mvPowerSeries_norm_coeff_mul_le_mul (pow_nonneg hc m) hc ih hF
private theorem mvPowerSeries_norm_coeff_pow_le_one {ι : Type} {F : MvPowerSeries ι K}
    (hF : ∀ e, ‖MvPowerSeries.coeff e F‖ ≤ 1) (m : ℕ) (e : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff e (F ^ m)‖ ≤ 1 := by
  simpa using mvPowerSeries_norm_coeff_pow_le_pow zero_le_one hF m e
private theorem mvPowerSeries_norm_coeff_pow_sub_pow_le {ι : Type} {A B : MvPowerSeries ι K} {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ e, ‖MvPowerSeries.coeff e A‖ ≤ 1) (hB : ∀ e, ‖MvPowerSeries.coeff e B‖ ≤ 1)
    (hAB : ∀ e, ‖MvPowerSeries.coeff e (A - B)‖ ≤ c) (m : ℕ) (e : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff e (A ^ m - B ^ m)‖ ≤ c := by
  classical
  have hs : ∀ e, ‖MvPowerSeries.coeff e (∑ i ∈ Finset.range m, A ^ i * B ^ (m - 1 - i))‖ ≤ 1 := by
    intro e
    rw [map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    simpa using mvPowerSeries_norm_coeff_mul_le_mul zero_le_one zero_le_one (mvPowerSeries_norm_coeff_pow_le_one hA i) (mvPowerSeries_norm_coeff_pow_le_one hB (m - 1 - i)) e
  rw [← geom_sum₂_mul]
  simpa using mvPowerSeries_norm_coeff_mul_le_mul zero_le_one hc hs hAB e
private theorem mvPowerSeries_norm_coeff_pow_prime_sub_le_mul_norm {ι : Type} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {A B : MvPowerSeries ι K}
    {c : ℝ} (hc : 0 ≤ c) (hcl : c ≤ ‖(l : K)‖) (hB : ∀ e, ‖MvPowerSeries.coeff e B‖ ≤ 1)
    (hAB : ∀ e, ‖MvPowerSeries.coeff e (A - B)‖ ≤ c) (e : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff e (A ^ l - B ^ l)‖ ≤ c * ‖(l : K)‖ := by
  classical
  obtain ⟨D, rfl⟩ : ∃ D, A = D + B := ⟨A - B, by ring⟩
  simp only [add_sub_cancel_right] at hAB
  have hc1 : c ≤ 1 := hcl.trans hl1.le
  have hl2 : 2 ≤ l := hl.two_le
  rw [add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
    add_sub_cancel_right]
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc (norm_nonneg _))
    fun i hi => ?_
  have hi' : i < l := Finset.mem_range.mp hi
  rw [← Nat.cast_comm, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, norm_mul]
  have hterm : ‖MvPowerSeries.coeff e (D ^ (i + 1) * B ^ (l - (i + 1)))‖ ≤ c ^ (i + 1) := by
    simpa using mvPowerSeries_norm_coeff_mul_le_mul (pow_nonneg hc _) zero_le_one (mvPowerSeries_norm_coeff_pow_le_pow hc hAB (i + 1)) (mvPowerSeries_norm_coeff_pow_le_one hB _) e
  have hch : ‖((l.choose (i + 1) : ℕ) : K)‖ * c ^ (i + 1) ≤ c * ‖(l : K)‖ := by
    obtain h | h : i + 1 < l ∨ i + 1 = l := by omega
    · obtain ⟨q, hq⟩ := hl.dvd_choose_self (Nat.succ_ne_zero i) h
      rw [hq, Nat.cast_mul, norm_mul]
      have hq1 : ‖(q : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K q
      have hpc : c ^ (i + 1) ≤ c := pow_le_of_le_one hc hc1 (Nat.succ_ne_zero i)
      calc ‖(l : K)‖ * ‖(q : K)‖ * c ^ (i + 1) ≤ ‖(l : K)‖ * 1 * c := by
            gcongr
        _ = c * ‖(l : K)‖ := by ring
    · rw [h, Nat.choose_self, Nat.cast_one, norm_one, one_mul]
      obtain ⟨j, rfl⟩ : ∃ j, l = j + 2 := ⟨l - 2, by omega⟩
      have hpc : c ^ (j + 1) ≤ c := pow_le_of_le_one hc hc1 (Nat.succ_ne_zero j)
      calc c ^ (j + 2) = c * c ^ (j + 1) := by ring
        _ ≤ c * ‖((j + 2 : ℕ) : K)‖ := by gcongr; exact hpc.trans hcl
  calc ‖((l.choose (i + 1) : ℕ) : K)‖ * ‖MvPowerSeries.coeff e (D ^ (i + 1) * B ^ (l - (i + 1)))‖
      ≤ ‖((l.choose (i + 1) : ℕ) : K)‖ * c ^ (i + 1) := by gcongr
    _ ≤ c * ‖(l : K)‖ := hch
private theorem mvPowerSeries_norm_coeff_pow_prime_pow_sub_le {ι : Type} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {P Q : MvPowerSeries ι K}
    (hQ : ∀ e, ‖MvPowerSeries.coeff e Q‖ ≤ 1)
    (hPQ : ∀ e, ‖MvPowerSeries.coeff e (P - Q)‖ ≤ ‖(l : K)‖) :
    ∀ (v : ℕ) (e : ι →₀ ℕ), ‖MvPowerSeries.coeff e (P ^ (l ^ v) - Q ^ (l ^ v))‖ ≤ ‖(l : K)‖ ^ (v + 1) := by
  intro v
  induction v with
  | zero => simpa using hPQ
  | succ v ih =>
    intro e
    rw [pow_succ, pow_mul, pow_mul, pow_succ _ (v + 1)]
    exact mvPowerSeries_norm_coeff_pow_prime_sub_le_mul_norm hl hl1 (pow_nonneg (norm_nonneg _) _)
      (pow_le_of_le_one (norm_nonneg _) hl1.le (Nat.succ_ne_zero v)) (mvPowerSeries_norm_coeff_pow_le_one hQ _) ih e
private theorem norm_natCast_eq_one_of_not_prime_dvd (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {m : ℕ} (hm : ¬ l ∣ m) :
    ‖(m : K)‖ = 1 := by
  have hcop : Nat.Coprime l m := (Nat.coprime_or_dvd_of_prime hl m).resolve_right hm
  have h1 := Nat.gcd_eq_gcd_ab l m
  rw [hcop.gcd_eq_one] at h1
  have h2 : (1 : K) = (l : K) * (Nat.gcdA l m : K) + (m : K) * (Nat.gcdB l m : K) := by
    have h3 := congrArg (fun x : ℤ => (x : K)) h1
    push_cast at h3
    exact h3
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K m) (not_lt.mp fun hlt => ?_)
  have h4 : ‖(1 : K)‖ < 1 := by
    rw [h2]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      calc ‖(l : K)‖ * ‖((Nat.gcdA l m : ℤ) : K)‖ ≤ ‖(l : K)‖ * 1 := by
            gcongr
            exact IsUltrametricDist.norm_intCast_le_one K _
        _ < 1 := by simpa using hl1
    · rw [norm_mul]
      calc ‖(m : K)‖ * ‖((Nat.gcdB l m : ℤ) : K)‖ ≤ ‖(m : K)‖ * 1 := by
            gcongr
            exact IsUltrametricDist.norm_intCast_le_one K _
        _ < 1 := by simpa using hlt
  simp at h4
end ReciprocityTheory.ChartRestriction.L1
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {ι : Type} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (z : PowerSeries K)
    (hz0 : constantCoeff z = 0) (hz : IntegralPS (derivative K z)) (P Q : MvPowerSeries ι K)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hQ0 : MvPowerSeries.constantCoeff Q = 0)
    (hP : IntegralMv P) (hQ : IntegralMv Q) (hPQ : DivByMv (l : K) (P - Q)) :
    DivByMv (l : K) (z.subst P - z.subst Q) := by
  classical
  have hPs : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  have hQs : PowerSeries.HasSubst Q := PowerSeries.HasSubst.of_constantCoeff_zero hQ0
  have hPi : ∀ e, ‖MvPowerSeries.coeff e P‖ ≤ 1 := by
    unfold IntegralMv at hP
    exact hP
  have hQi : ∀ e, ‖MvPowerSeries.coeff e Q‖ ≤ 1 := by
    unfold IntegralMv at hQ
    exact hQ
  have hPQi : ∀ e, ‖MvPowerSeries.coeff e (P - Q)‖ ≤ ‖(l : K)‖ := by
    unfold DivByMv at hPQ
    exact hPQ
  have hzi : ∀ n, ‖PowerSeries.coeff n (derivative K z)‖ ≤ 1 := by
    unfold IntegralPS at hz
    exact hz
  have hpow := mvPowerSeries_norm_coeff_pow_prime_pow_sub_le hl hl1 hQi hPQi
  have hterm : ∀ (d : ℕ) (e : ι →₀ ℕ),
      ‖PowerSeries.coeff d z • MvPowerSeries.coeff e (P ^ d) -
        PowerSeries.coeff d z • MvPowerSeries.coeff e (Q ^ d)‖ ≤ ‖(l : K)‖ := by
    intro d e
    rw [← smul_sub, ← map_sub, norm_smul]
    rcases d with _ | k
    · have h0 : PowerSeries.coeff 0 z = 0 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact hz0
      rw [h0, norm_zero, zero_mul]
      exact norm_nonneg _
    · obtain ⟨v, m, hm, hkm0⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.succ_ne_zero k) l hl.ne_one
      have hkm : k + 1 = l ^ v * m := hkm0
      have hz' : ‖PowerSeries.coeff (k + 1) z‖ * ‖((k + 1 : ℕ) : K)‖ ≤ 1 := by
        have h1 := hzi k
        rw [PowerSeries.coeff_derivative] at h1
        simpa [norm_mul] using h1
      have hn : ‖((k + 1 : ℕ) : K)‖ = ‖(l : K)‖ ^ v := by
        rw [hkm, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, norm_natCast_eq_one_of_not_prime_dvd hl hl1 hm, mul_one]
      have hPQn : ‖MvPowerSeries.coeff e (P ^ (k + 1) - Q ^ (k + 1))‖ ≤ ‖(l : K)‖ ^ (v + 1) := by
        rw [hkm, pow_mul, pow_mul]
        exact mvPowerSeries_norm_coeff_pow_sub_pow_le (pow_nonneg (norm_nonneg _) _) (mvPowerSeries_norm_coeff_pow_le_one hPi _) (mvPowerSeries_norm_coeff_pow_le_one hQi _) (hpow v) m e
      calc ‖PowerSeries.coeff (k + 1) z‖ * ‖MvPowerSeries.coeff e (P ^ (k + 1) - Q ^ (k + 1))‖
          ≤ ‖PowerSeries.coeff (k + 1) z‖ * ‖(l : K)‖ ^ (v + 1) := by gcongr
        _ = (‖PowerSeries.coeff (k + 1) z‖ * ‖((k + 1 : ℕ) : K)‖) * ‖(l : K)‖ := by
          rw [hn, pow_succ, mul_assoc]
        _ ≤ 1 * ‖(l : K)‖ := by gcongr
        _ = ‖(l : K)‖ := one_mul _
  unfold DivByMv
  intro e
  rw [map_sub, PowerSeries.coeff_subst hPs, PowerSeries.coeff_subst hQs,
    ← finsum_sub_distrib (PowerSeries.coeff_subst_finite hPs z e)
      (PowerSeries.coeff_subst_finite hQs z e)]
  exact norm_finsum_le_of_forall_norm_le_univ_sort _ (norm_nonneg _) fun d => hterm d e
end ReciprocityTheory.ChartRestriction.L1
