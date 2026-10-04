-- Prove2me | solution 1 for SennottDP.DiscountedASM.firstPassageDisc_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:25:44.745154+00:00
-- url     : https://prove2.me/submissions/6a26baa4-be94-40ae-90c5-2402f61c9cba

import Mathlib
import Definitions.Def_SennottDP_DiscountedASM_MDC
import Definitions.Def_SennottDP_DiscountedASM_ApproxSeq
import Definitions.Def_SennottDP_DiscountedASM_tabooProb

open scoped ENNReal NNReal
open Classical Filter Topology

namespace SennottDP.DiscountedASM.FPD

open MDC

variable {S Act : Type} (M : MDC S Act)

theorem fpd_step_one (f : S → Act) (i j : S) : M.stepProb f 1 i j = M.P i (f i) j := by
  show ∑' k, M.P i (f i) k * M.stepProb f 0 k j = _
  have : ∀ k, M.P i (f i) k * M.stepProb f 0 k j = if k = j then M.P i (f i) j else 0 := by
    intro k
    show M.P i (f i) k * (if k = j then 1 else 0) = _
    split_ifs with h
    · rw [h, mul_one]
    · rw [mul_zero]
  rw [tsum_congr this, tsum_ite_eq]

theorem fpd_taboo_le (T : Finset S) (f : S → Act) :
    ∀ t i j, M.tabooProb T f (t + 1) i j ≤ M.stepProb f (t + 1) i j := by
  intro t
  induction t with
  | zero => intro i j; rw [fpd_step_one]; exact le_rfl
  | succ t ih =>
    intro i j
    show (∑' k, (if k ∈ T then M.P i (f i) k * M.tabooProb T f (t + 1) k j else 0)) ≤
      ∑' k, M.P i (f i) k * M.stepProb f (t + 1) k j
    refine ENNReal.tsum_le_tsum fun k => ?_
    split_ifs
    · exact mul_le_mul_of_nonneg_left (ih k j) bot_le
    · exact bot_le

theorem fpd_step_sum (f : S → Act) (hf : ∀ i, f i ∈ M.A i) :
    ∀ t i, ∑' j, M.stepProb f t i j ≤ 1 := by
  intro t
  induction t with
  | zero =>
    intro i
    show ∑' j, (if i = j then (1 : ℝ≥0∞) else 0) ≤ 1
    rw [show (fun j => if i = j then (1 : ℝ≥0∞) else 0) = fun j => if j = i then 1 else 0 from
      funext fun j => by simp [eq_comm], tsum_ite_eq]
  | succ t ih =>
    intro i
    show ∑' j, ∑' k, M.P i (f i) k * M.stepProb f t k j ≤ 1
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    calc ∑' k, M.P i (f i) k * ∑' j, M.stepProb f t k j ≤ ∑' k, M.P i (f i) k * 1 :=
          ENNReal.tsum_le_tsum fun k => mul_le_mul_of_nonneg_left (ih k) bot_le
      _ = 1 := by simp only [mul_one]; exact M.P_sum i (f i) (hf i)

end SennottDP.DiscountedASM.FPD

open SennottDP.DiscountedASM SennottDP.DiscountedASM.FPD in
theorem solution {S Act : Type} [Countable S] (M : MDC S Act)
    (Δs : ApproxSeq M) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (e : S → Act) (he : ∀ i, e i ∈ M.A i) (i : S) :
    Tendsto (fun N => M.firstPassageDisc (Δs.SN N) e α i) atTop (𝓝 0) := by
  set a : ℕ → S → ℝ≥0∞ := fun n j => M.stepProb e (n + 1) i j with ha
  have ha1 : ∀ n, ∑' j, a n j ≤ 1 := fun n => fpd_step_sum M e he (n + 1) i
  set p : ℕ → ℕ → ℝ≥0∞ := fun N n =>
    ∑' j : S, (if j ∈ Δs.SN N then 0 else M.tabooProb (Δs.SN N) e (n + 1) i j) with hp
  set q : ℕ → ℕ → ℝ≥0∞ := fun N n => ∑' j : S, (if j ∈ Δs.SN N then 0 else a n j) with hq
  have hpq : ∀ N n, p N n ≤ q N n := fun N n =>
    ENNReal.tsum_le_tsum fun j => by
      split_ifs
      · exact le_rfl
      · exact fpd_taboo_le M _ e n i j
  have hq1 : ∀ N n, q N n ≤ 1 := fun N n =>
    (ENNReal.tsum_le_tsum fun j => by split_ifs <;> simp).trans (ha1 n)
  -- each `q · n` tends to zero
  have hqlim : ∀ n, Tendsto (fun N => q N n) atTop (𝓝 0) := by
    intro n
    have hfin : ∑' j, a n j ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (ha1 n)
    have h := ENNReal.tendsto_tsum_compl_atTop_zero hfin
    rw [ENNReal.tendsto_nhds_zero] at h ⊢
    intro ε hε
    obtain ⟨F, hF⟩ := Filter.eventually_atTop.mp (h ε hε)
    have hev : ∀ᶠ N in atTop, F ⊆ Δs.SN N := by
      have : ∀ x ∈ F, ∀ᶠ N in atTop, x ∈ Δs.SN N := by
        intro x _
        obtain ⟨Nx, hNx0, hx⟩ := Δs.SN_cover x
        filter_upwards [eventually_ge_atTop Nx] with N hN
        exact Δs.SN_mono Nx N hNx0 hN hx
      filter_upwards [(Filter.eventually_all_finset F).mpr this] with N hN
      exact fun x hx => hN x hx
    filter_upwards [hev] with N hN
    have h1 := hF (Δs.SN N) hN
    have h2 : ∑' b : {x // x ∉ Δs.SN N}, a n b =
        ∑' j, Set.indicator {x | x ∉ Δs.SN N} (a n) j := tsum_subtype {x | x ∉ Δs.SN N} (a n)
    have h3 : q N n = ∑' b : {x // x ∉ Δs.SN N}, a n b := by
      rw [h2, hq]
      refine tsum_congr fun j => ?_
      by_cases hj : j ∈ Δs.SN N <;> simp [Set.indicator_apply, hj]
    rw [h3]; exact h1
  have hα1' : (α : ℝ≥0∞) < 1 := by exact_mod_cast hα1
  have hgeo_ne : (1 - (α : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hα1').ne'
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have htail : Tendsto (fun m : ℕ => (α : ℝ≥0∞) ^ (m + 1) * (1 - (α : ℝ≥0∞))⁻¹) atTop (𝓝 0) := by
    have h0 : Tendsto (fun m : ℕ => (α : ℝ≥0∞) ^ (m + 1)) atTop (𝓝 0) :=
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hα1').comp (tendsto_add_atTop_nat 1)
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hgeo_ne)
  obtain ⟨m, hm⟩ := (ENNReal.tendsto_nhds_zero.mp htail (ε / 2) hε2).exists
  have hsum : Tendsto (fun N => ∑ n ∈ Finset.range m, q N n) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range m) (fun n _ => hqlim n)
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hsum (ε / 2) hε2] with N hN
  show (∑' n : ℕ, (α : ℝ≥0∞) ^ (n + 1) * p N n) ≤ ε
  rw [← Summable.sum_add_tsum_nat_add' (k := m) ENNReal.summable]
  have hαle : ∀ n, (α : ℝ≥0∞) ^ n ≤ 1 := fun n => pow_le_one₀ bot_le hα1'.le
  calc ∑ n ∈ Finset.range m, (α : ℝ≥0∞) ^ (n + 1) * p N n +
        ∑' n, (α : ℝ≥0∞) ^ (n + m + 1) * p N (n + m)
      ≤ ∑ n ∈ Finset.range m, q N n + ∑' n : ℕ, (α : ℝ≥0∞) ^ n * (α : ℝ≥0∞) ^ (m + 1) := by
        refine add_le_add (Finset.sum_le_sum fun n _ => ?_) (ENNReal.tsum_le_tsum fun n => ?_)
        · calc (α : ℝ≥0∞) ^ (n + 1) * p N n ≤ 1 * q N n :=
                mul_le_mul' (hαle _) (hpq N n)
            _ = q N n := one_mul _
        · calc (α : ℝ≥0∞) ^ (n + m + 1) * p N (n + m) ≤ (α : ℝ≥0∞) ^ (n + m + 1) * 1 :=
                mul_le_mul_of_nonneg_left ((hpq N _).trans (hq1 N _)) bot_le
            _ = (α : ℝ≥0∞) ^ n * (α : ℝ≥0∞) ^ (m + 1) := by rw [mul_one, ← pow_add]; ring_nf
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_comm]
        exact hm
    _ = ε := ENNReal.add_halves ε


