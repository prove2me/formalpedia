-- Prove2me | solution 1 for ProcessingNetworks.FluidStability.uniform_slln_service_completions
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:04:05.586977+00:00
-- url     : https://prove2.me/submissions/c0eb0cba-d529-46db-91f7-e927caf50af6

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidStability_SPNProcessFamily

set_option autoImplicit false

open Filter in
theorem P2M1ff5510b_split_sum (N0 : ℕ) (a b : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (if k < N0 then a k else b (k - N0)) =
      ∑ k ∈ Finset.range (min n N0), a k + ∑ l ∈ Finset.range (n - N0), b l := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : n < N0
    · rw [if_pos h, Nat.min_eq_left (by omega : n + 1 ≤ N0), Nat.min_eq_left (by omega : n ≤ N0),
        show n + 1 - N0 = n - N0 by omega, Finset.sum_range_succ]
      ring
    · rw [if_neg h, Nat.min_eq_right (by omega : N0 ≤ n + 1), Nat.min_eq_right (by omega : N0 ≤ n),
        show n + 1 - N0 = (n - N0) + 1 by omega, Finset.sum_range_succ]
      ring

open Filter Topology in
theorem P2M1ff5510b_shift (s : ℕ → ℝ) (L : ℝ)
    (h : Tendsto (fun n : ℕ => s n / n) atTop (𝓝 L)) (d : ℕ) :
    Tendsto (fun n : ℕ => s (n - d) / n) atTop (𝓝 L) := by
  have h1 : Tendsto (fun n : ℕ => s (n - d) / ((n - d : ℕ) : ℝ)) atTop (𝓝 L) :=
    h.comp (tendsto_sub_atTop_nat d)
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) - (d : ℝ) / n) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (d : ℝ))
  rw [sub_zero] at h2
  have h3 := h1.mul h2
  rw [mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (d + 1)] with n hn
  have hnd : ((n - d : ℕ) : ℝ) = (n : ℝ) - d := by
    rw [Nat.cast_sub (by omega)]
  have hpos : (0 : ℝ) < (n : ℝ) - d := by
    have : (d : ℝ) + 1 ≤ n := by exact_mod_cast hn
    linarith
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    exact this.ne'
  rw [hnd]
  field_simp

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability ProcessingNetworks.FluidStability in
theorem solution
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ) (ω : Ω)
    (h215 :
      ∀ j, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop (nhds (dat.m j)))
    (j : Fin J) :
    ∀ ε : ℝ, 0 < ε → ∃ Nb : ℕ, ∀ n ≥ Nb, ∀ x : Xstate,
      |(n : ℝ)⁻¹ * spnV fam x j n ω - dat.m j| < ε := by
  intro ε hε
  obtain ⟨κ, hκ⟩ := fam.service_bound
  have hN0 : ∀ x, (Mrep.f x).1 j ≤ κ := by
    intro x
    have := (fam.relations x).N_init ω
    have h := hκ x 0 ω j
    rw [this] at h
    exact h
  set C0 : ℝ := ∑ p ∈ fam.pool, |(p ω).1| with hC0
  have hC0nn : 0 ≤ C0 := Finset.sum_nonneg (fun p _ => abs_nonneg _)
  set s : ℕ → ℝ := fun m => ∑ ℓ ∈ Finset.range m, v j ℓ ω with hs
  -- decomposition
  have hdec : ∀ x n, spnV fam x j n ω =
      ∑ k ∈ Finset.range (min n ((Mrep.f x).1 j)), (fam.Psi x j k ω).1 +
        s (n - (Mrep.f x).1 j) := by
    intro x n
    unfold spnV delayedWalk
    rw [← P2M1ff5510b_split_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold delayedTerm
    split_ifs <;> rfl
  have hres : ∀ x n, |∑ k ∈ Finset.range (min n ((Mrep.f x).1 j)), (fam.Psi x j k ω).1|
      ≤ κ * C0 := by
    intro x n
    calc |∑ k ∈ Finset.range (min n ((Mrep.f x).1 j)), (fam.Psi x j k ω).1|
        ≤ ∑ k ∈ Finset.range (min n ((Mrep.f x).1 j)), |(fam.Psi x j k ω).1| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (min n ((Mrep.f x).1 j)), C0 := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hk' : k < (Mrep.f x).1 j := by
            rw [Finset.mem_range] at hk
            omega
          have hmem := fam.Psi_mem_pool x j k hk'
          exact Finset.single_le_sum (f := fun p : Ω → ℝ × (Fin I → ℕ) => |(p ω).1|)
            (fun p _ => abs_nonneg _) hmem
      _ = (min n ((Mrep.f x).1 j) : ℕ) * C0 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ κ * C0 := by
          apply mul_le_mul_of_nonneg_right _ hC0nn
          exact_mod_cast (min_le_right _ _).trans (hN0 x)
  have hε2 : 0 < ε / 2 := by linarith
  have e1 : ∀ᶠ n in atTop, ∀ d : Fin (κ + 1), dist (s (n - (d : ℕ)) / n) (dat.m j) < ε / 2 := by
    rw [Filter.eventually_all]
    intro d
    exact (Metric.tendsto_nhds.1 (P2M1ff5510b_shift s (dat.m j) (h215 j) d)) (ε / 2) hε2
  have e2 : ∀ᶠ n : ℕ in atTop, ((κ : ℝ) * C0) / n < ε / 2 :=
    (tendsto_order.1 (tendsto_const_div_atTop_nhds_zero_nat ((κ : ℝ) * C0))).2 _ hε2
  have e3 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨Nb, hNb⟩ := Filter.eventually_atTop.1 (e1.and (e2.and e3))
  refine ⟨Nb, fun n hn x => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hNb n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast h3
  have hd := h1 ⟨(Mrep.f x).1 j, Nat.lt_succ_of_le (hN0 x)⟩
  simp only [Real.dist_eq] at hd
  rw [hdec x n]
  set R := ∑ k ∈ Finset.range (min n ((Mrep.f x).1 j)), (fam.Psi x j k ω).1 with hR
  have hRb := hres x n
  rw [← hR] at hRb
  have hsplit : (n : ℝ)⁻¹ * (R + s (n - (Mrep.f x).1 j)) - dat.m j =
      R / n + (s (n - (Mrep.f x).1 j) / n - dat.m j) := by
    field_simp
    ring
  rw [hsplit]
  have hRn : |R / n| ≤ (κ * C0) / n := by
    rw [abs_div, abs_of_pos hnpos]
    exact div_le_div_of_nonneg_right hRb hnpos.le
  calc |R / n + (s (n - (Mrep.f x).1 j) / n - dat.m j)|
      ≤ |R / n| + |s (n - (Mrep.f x).1 j) / n - dat.m j| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring
