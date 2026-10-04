-- Prove2me | solution 1 for SennottDP.Tauberian.abelian_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:53:00.446752+00:00
-- url     : https://prove2.me/submissions/3d497f8f-a73e-4a26-abee-be15009b42a8

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Cauchy product: `(∑ α^n) U(α) = ∑ α^n w_{n+1}` (no finiteness needed in `[0,∞]`). -/
theorem abelian_inequalities_key (u : ℕ → ℝ≥0∞) (α : ℝ≥0) :
    (∑' n : ℕ, (α : ℝ≥0∞) ^ n) * U u α = ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1) := by
  have hterm : ∀ n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1)
      = ∑' k : ℕ, (if k ≤ n then (α : ℝ≥0∞) ^ n * u k else 0) := by
    intro n
    unfold w
    rw [Finset.mul_sum, tsum_eq_sum (s := Finset.range (n + 1))]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
    · intro k hk
      rw [if_neg]
      intro hkn
      exact hk (Finset.mem_range.mpr (Nat.lt_succ_of_le hkn))
  have hinner : ∀ k : ℕ, ∑' n : ℕ, (if k ≤ n then (α : ℝ≥0∞) ^ n * u k else 0)
      = (∑' m : ℕ, (α : ℝ≥0∞) ^ m) * ((α : ℝ≥0∞) ^ k * u k) := by
    intro k
    have hsupp : Function.support (fun n : ℕ => if k ≤ n then (α : ℝ≥0∞) ^ n * u k else 0)
        ⊆ Set.range (fun m : ℕ => m + k) := by
      intro n hn
      by_cases hkn : k ≤ n
      · exact ⟨n - k, Nat.sub_add_cancel hkn⟩
      · rw [Function.mem_support] at hn
        exact (hn (by simp [hkn])).elim
    rw [← ENNReal.tsum_mul_right, ← (add_left_injective k).tsum_eq hsupp]
    refine tsum_congr fun m => ?_
    rw [if_pos (Nat.le_add_left k m), pow_add]
    ring
  unfold U
  simp_rw [hterm]
  rw [ENNReal.tsum_comm]
  simp_rw [hinner]
  rw [ENNReal.tsum_mul_left]

/-- `abelMean u α = (1-α) * ((1-α) * ∑ α^n w_{n+1})` for `α < 1`. -/
theorem abelian_inequalities_abel_eq (u : ℕ → ℝ≥0∞) (α : ℝ≥0) (hα : α < 1) :
    abelMean u α = (1 - (α : ℝ≥0∞)) *
      ((1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1)) := by
  have hα' : (α : ℝ≥0∞) < 1 := by exact_mod_cast hα
  have h0 : (1 - (α : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt hα').ne'
  have ht : (1 - (α : ℝ≥0∞)) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  rw [← abelian_inequalities_key, ENNReal.tsum_geometric,
    ← mul_assoc (1 - (α : ℝ≥0∞)) (1 - (α : ℝ≥0∞))⁻¹, ENNReal.mul_inv_cancel h0 ht, one_mul]
  rfl

theorem abelian_inequalities_w_one (k : ℕ) : w (fun _ => (1 : ℝ≥0∞)) k = (k : ℝ≥0∞) := by
  simp [w]

theorem abelian_inequalities_abel_one (α : ℝ≥0) (hα : α < 1) :
    abelMean (fun _ => (1 : ℝ≥0∞)) α = 1 := by
  have hα' : (α : ℝ≥0∞) < 1 := by exact_mod_cast hα
  have h0 : (1 - (α : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt hα').ne'
  have ht : (1 - (α : ℝ≥0∞)) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  simp only [abelMean, U, mul_one]
  rw [ENNReal.tsum_geometric, ENNReal.mul_inv_cancel h0 ht]

/-- `(1 - α) * K → 0` as `α → 1⁻`, for finite `K`. -/
theorem abelian_inequalities_tendsto (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    Tendsto (fun α : ℝ≥0 => (1 - (α : ℝ≥0∞)) * K) (𝓝[<] (1 : ℝ≥0)) (𝓝 0) := by
  lift K to ℝ≥0 using hK
  have h : Tendsto (fun α : ℝ≥0 => (1 - α) * K) (𝓝 (1 : ℝ≥0)) (𝓝 ((1 - 1) * K)) :=
    ((continuous_const.sub continuous_id).mul continuous_const).tendsto 1
  rw [tsub_self, zero_mul] at h
  have h2 := (ENNReal.tendsto_coe.mpr h).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
  refine h2.congr fun α => ?_
  simp [ENNReal.coe_sub]

theorem abelian_inequalities_upper (u : ℕ → ℝ≥0∞) :
    limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (cesaroMean u) atTop := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hL => ?_
  set L := limsup (cesaroMean u) atTop
  have hε2 : (0 : ℝ≥0∞) < ((ε / 2 : ℝ≥0) : ℝ≥0∞) := by
    have : (0 : ℝ≥0) < ε / 2 := half_pos hε
    exact_mod_cast this
  have hM : L < L + ((ε / 2 : ℝ≥0) : ℝ≥0∞) := ENNReal.lt_add_right hL.ne hε2.ne'
  set M := L + ((ε / 2 : ℝ≥0) : ℝ≥0∞)
  have hMtop : M ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hL.ne, ENNReal.coe_ne_top⟩
  have hev := eventually_lt_of_limsup_lt hM
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  set N := N0 + 1
  have hwn : ∀ n, N ≤ n → w u n ≤ M * n := by
    intro n hn
    have h1 := hN0 n (by omega)
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact (ENNReal.div_lt_iff (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n))).mp h1 |>.le
  set C := w u N
  have hC : C ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top hMtop (ENNReal.natCast_ne_top N))
    (hwn N le_rfl)
  have hbound : ∀ n : ℕ, w u (n + 1) ≤ C + M * w (fun _ => (1 : ℝ≥0∞)) (n + 1) := by
    intro n
    rw [abelian_inequalities_w_one]
    by_cases h : n + 1 ≤ N
    · refine le_trans ?_ le_self_add
      exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)
    · refine le_trans ?_ le_add_self
      exact hwn (n + 1) (by omega)
  have hev2 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), (1 - (α : ℝ≥0∞)) * C < ((ε / 2 : ℝ≥0) : ℝ≥0∞) :=
    (abelian_inequalities_tendsto C hC).eventually (gt_mem_nhds hε2)
  have hev3 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), α < 1 := self_mem_nhdsWithin
  have hfin : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), abelMean u α ≤ L + ε := by
    filter_upwards [hev2, hev3] with α h2 h3
    have hα' : (α : ℝ≥0∞) < 1 := by exact_mod_cast h3
    have h0 : (1 - (α : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt hα').ne'
    have ht : (1 - (α : ℝ≥0∞)) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
    have hS : ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1) ≤
        C * ∑' n : ℕ, (α : ℝ≥0∞) ^ n +
          M * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w (fun _ => (1 : ℝ≥0∞)) (n + 1) := by
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun n => ?_
      calc (α : ℝ≥0∞) ^ n * w u (n + 1)
          ≤ (α : ℝ≥0∞) ^ n * (C + M * w (fun _ => (1 : ℝ≥0∞)) (n + 1)) := by
            gcongr; exact hbound n
        _ = _ := by ring
    have hone := abelian_inequalities_abel_one α h3
    rw [abelian_inequalities_abel_eq _ α h3] at hone
    have hgeo : (1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n = 1 := by
      rw [ENNReal.tsum_geometric, ENNReal.mul_inv_cancel h0 ht]
    rw [abelian_inequalities_abel_eq _ α h3]
    calc (1 - (α : ℝ≥0∞)) * ((1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1))
        ≤ (1 - (α : ℝ≥0∞)) * ((1 - (α : ℝ≥0∞)) * (C * ∑' n : ℕ, (α : ℝ≥0∞) ^ n +
          M * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w (fun _ => (1 : ℝ≥0∞)) (n + 1))) := by
          gcongr
      _ = (1 - (α : ℝ≥0∞)) * C * ((1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n) +
          M * ((1 - (α : ℝ≥0∞)) * ((1 - (α : ℝ≥0∞)) *
            ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w (fun _ => (1 : ℝ≥0∞)) (n + 1))) := by ring
      _ = (1 - (α : ℝ≥0∞)) * C + M := by rw [hgeo, hone, mul_one, mul_one]
      _ ≤ ((ε / 2 : ℝ≥0) : ℝ≥0∞) + M := by gcongr
      _ = L + ε := by
          rw [add_comm, add_assoc, ← ENNReal.coe_add, add_halves]
  exact limsup_le_of_le (by isBoundedDefault) hfin

theorem abelian_inequalities_lower (u : ℕ → ℝ≥0∞) :
    liminf (cesaroMean u) atTop ≤ liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) := by
  refine le_of_forall_lt_imp_le_of_dense fun m hm => ?_
  have hmtop : m ≠ ⊤ := ne_top_of_lt hm
  have hev := eventually_lt_of_lt_liminf hm
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  set N := N0 + 1
  have hwn : ∀ n, N ≤ n → m * n ≤ w u n := by
    intro n hn
    have h1 := hN0 n (by omega)
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact ((ENNReal.lt_div_iff_mul_lt (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n))).mp h1).le
  have hbound : ∀ n : ℕ, m * w (fun _ => (1 : ℝ≥0∞)) (n + 1) ≤ w u (n + 1) + m * N := by
    intro n
    rw [abelian_inequalities_w_one]
    by_cases h : n + 1 ≤ N
    · refine le_trans ?_ le_add_self
      gcongr
    · refine le_trans ?_ le_self_add
      exact hwn (n + 1) (by omega)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  have hK : m * N ≠ ⊤ := ENNReal.mul_ne_top hmtop (ENNReal.natCast_ne_top N)
  have hev2 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), (1 - (α : ℝ≥0∞)) * (m * N) < ε :=
    (abelian_inequalities_tendsto _ hK).eventually (gt_mem_nhds hε')
  have hev3 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), α < 1 := self_mem_nhdsWithin
  have hfin : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), m - ε ≤ abelMean u α := by
    filter_upwards [hev2, hev3] with α h2 h3
    have hα' : (α : ℝ≥0∞) < 1 := by exact_mod_cast h3
    have h0 : (1 - (α : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt hα').ne'
    have ht : (1 - (α : ℝ≥0∞)) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
    have hS : m * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w (fun _ => (1 : ℝ≥0∞)) (n + 1) ≤
        ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1) + (m * N) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n := by
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun n => ?_
      calc m * ((α : ℝ≥0∞) ^ n * w (fun _ => (1 : ℝ≥0∞)) (n + 1))
          = (α : ℝ≥0∞) ^ n * (m * w (fun _ => (1 : ℝ≥0∞)) (n + 1)) := by ring
        _ ≤ (α : ℝ≥0∞) ^ n * (w u (n + 1) + m * N) := by gcongr; exact hbound n
        _ = _ := by ring
    have hone := abelian_inequalities_abel_one α h3
    rw [abelian_inequalities_abel_eq _ α h3] at hone
    have hgeo : (1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n = 1 := by
      rw [ENNReal.tsum_geometric, ENNReal.mul_inv_cancel h0 ht]
    rw [abelian_inequalities_abel_eq _ α h3, tsub_le_iff_right]
    calc m = m * ((1 - (α : ℝ≥0∞)) * ((1 - (α : ℝ≥0∞)) *
            ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w (fun _ => (1 : ℝ≥0∞)) (n + 1))) := by
          rw [hone, mul_one]
      _ = (1 - (α : ℝ≥0∞)) * ((1 - (α : ℝ≥0∞)) * (m *
            ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w (fun _ => (1 : ℝ≥0∞)) (n + 1))) := by ring
      _ ≤ (1 - (α : ℝ≥0∞)) * ((1 - (α : ℝ≥0∞)) * (∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1) +
            (m * N) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n)) := by gcongr
      _ = (1 - (α : ℝ≥0∞)) * ((1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * w u (n + 1)) +
            (1 - (α : ℝ≥0∞)) * (m * N) * ((1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n) := by
          ring
      _ ≤ _ := by rw [hgeo, mul_one]; gcongr
  have := le_liminf_of_le (by isBoundedDefault) hfin
  exact tsub_le_iff_right.mp this

end SennottDP.Tauberian

open SennottDP.Tauberian in
theorem solution (u : ℕ → ℝ≥0∞) (_hu0 : u 0 ≠ ⊤) :
    liminf (cesaroMean u) atTop ≤ liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
      liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
      limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (cesaroMean u) atTop := by
  have : (𝓝[<] (1 : ℝ≥0)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, zero_lt_one⟩
  exact ⟨abelian_inequalities_lower u, liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault),
    abelian_inequalities_upper u⟩


