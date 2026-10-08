-- Prove2me | solution 1 for ServiceParts.Allocation.pwl_convex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T15:01:43.685899+00:00
-- url     : https://prove2.me/submissions/abb7416a-dc13-4ec3-b445-dc46be524f46

import Mathlib
import Definitions.Def_ServiceParts_Allocation_AllocData

set_option autoImplicit false

open ServiceParts.Allocation in
theorem pwl_convex_grid_nonneg {Mbar : ℕ} (d : AllocData Mbar) (hd : d.WellFormed)
    (m : Fin Mbar) : ∀ j : ℕ, j ≤ d.n m → (0 : ℤ) ≤ d.grid m j := by
  intro j
  induction j with
  | zero => intro _; rw [hd.grid_zero m]
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 := hd.grid_strictMono m j (by omega)
    omega

open ServiceParts.Allocation in
theorem pwl_convex_slope_mono {Mbar : ℕ} (d : AllocData Mbar) (hd : d.WellFormed)
    (m : Fin Mbar) (k : ℕ) (hk : k < d.n m) :
    d.slope m k ≤ d.slope m (k + 1) := by
  by_cases hk1 : k + 1 < d.n m
  · obtain ⟨φ, hφ, hc⟩ := hd.cost_convex m
    unfold AllocData.slope
    rw [if_pos hk, if_pos hk1]
    rw [hc k (by omega), hc (k + 1) (by omega), hc (k + 1 + 1) (by omega)]
    have g0 := pwl_convex_grid_nonneg d hd m k (by omega)
    have g2 := pwl_convex_grid_nonneg d hd m (k + 1 + 1) (by omega)
    have s1 := hd.grid_strictMono m k hk
    have s2 := hd.grid_strictMono m (k + 1) hk1
    have hx : ((d.grid m k : ℤ) : ℝ) ∈ Set.Ici (0 : ℝ) := by
      simp only [Set.mem_Ici]; exact_mod_cast g0
    have hz : ((d.grid m (k + 1 + 1) : ℤ) : ℝ) ∈ Set.Ici (0 : ℝ) := by
      simp only [Set.mem_Ici]; exact_mod_cast g2
    exact hφ.slope_mono_adjacent hx hz (by exact_mod_cast s1) (by exact_mod_cast s2)
  · have hkn : k + 1 = d.n m := by omega
    unfold AllocData.slope
    rw [if_pos hk, if_neg hk1]
    have : d.n m - 1 = k := by omega
    rw [this, hkn]

theorem pwl_convex_telescope (s h : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, s k * (h k - h (k + 1))) + s N * h N =
      s 0 * h 0 + ∑ k ∈ Finset.range N, (s (k + 1) - s k) * h (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linear_combination ih

theorem pwl_convex_hinge (a : ℝ) : ConvexOn ℝ Set.univ (fun r : ℝ => max (r - a) 0) := by
  have h1 : ConvexOn ℝ Set.univ (fun r : ℝ => r - a) :=
    (convexOn_id convex_univ).sub (concaveOn_const a convex_univ)
  exact (h1.sup (convexOn_const 0 convex_univ)).congr (fun x _ => rfl)

theorem pwl_convex_sum (c a : ℕ → ℝ) (N : ℕ) (hc : ∀ k, k < N → 0 ≤ c k) :
    ConvexOn ℝ Set.univ (fun r : ℝ => ∑ k ∈ Finset.range N, c k * max (r - a k) 0) := by
  induction N with
  | zero => simpa using convexOn_const (0 : ℝ) convex_univ
  | succ N ih =>
    have h1 := ih (fun k hk => hc k (by omega))
    have h2 := (pwl_convex_hinge (a N)).smul (hc N (by omega))
    refine (h1.add h2).congr ?_
    intro x _
    simp [Finset.sum_range_succ, smul_eq_mul]

theorem pwl_convex_term (s gk gk1 r : ℝ) (hg : gk < gk1) :
    (if gk ≤ r then (min r gk1 - gk) * s else 0) =
      s * (max (r - gk) 0 - max (r - gk1) 0) := by
  split_ifs with h
  · rcases le_total r gk1 with h' | h'
    · rw [min_eq_left h', max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    · rw [min_eq_right h', max_eq_left (by linarith), max_eq_left (by linarith)]; ring
  · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; ring

theorem pwl_convex_last (s g r : ℝ) :
    (if g ≤ r then (r - g) * s else 0) = s * max (r - g) 0 := by
  split_ifs with h
  · rw [max_eq_left (by linarith)]; ring
  · rw [max_eq_right (by linarith)]; ring

open ServiceParts.Allocation in
theorem solution {Mbar : ℕ} (d : AllocData Mbar) (hd : d.WellFormed) (m : Fin Mbar) :
    ConvexOn ℝ (Set.Ici 0) (d.pwl m) := by
  set N := d.n m with hN
  set s : ℕ → ℝ := fun k => d.slope m k with hs
  set g : ℕ → ℝ := fun k => (d.grid m k : ℝ) with hg
  set h : ℝ → ℕ → ℝ := fun r k => max (r - g k) 0 with hh
  have hcoef : ∀ k, k < N → 0 ≤ s (k + 1) - s k := by
    intro k hk
    have := pwl_convex_slope_mono d hd m k hk
    simp only [hs]; linarith
  have hlin : ConvexOn ℝ Set.univ (fun r : ℝ => d.cost m 0 + s 0 * r) := by
    have := ((convexOn_const (d.cost m 0) convex_univ).add
      ((LinearMap.lsmul ℝ ℝ (s 0)).convexOn convex_univ))
    refine this.congr ?_
    intro x _
    simp
  have hF : ConvexOn ℝ Set.univ (fun r : ℝ => d.cost m 0 + s 0 * r +
      ∑ k ∈ Finset.range N, (s (k + 1) - s k) * max (r - g (k + 1)) 0) :=
    hlin.add (pwl_convex_sum (fun k => s (k + 1) - s k) (fun k => g (k + 1)) N hcoef)
  refine (hF.subset (Set.subset_univ _) (convex_Ici 0)).congr ?_
  intro r hr
  simp only [Set.mem_Ici] at hr
  have hg0 : g 0 = 0 := by simp [hg, hd.grid_zero m]
  have hstep : ∀ k, k < N → g k < g (k + 1) := by
    intro k hk
    have := hd.grid_strictMono m k hk
    simp only [hg]; exact_mod_cast this
  unfold AllocData.pwl
  have hsum : (∑ k ∈ Finset.range (d.n m),
        if (d.grid m k : ℝ) ≤ r then (min r (d.grid m (k + 1) : ℝ) - d.grid m k) * d.slope m k
        else 0) = ∑ k ∈ Finset.range N, s k * (h r k - h r (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    exact pwl_convex_term (s k) (g k) (g (k + 1)) r (hstep k hk)
  rw [hsum, pwl_convex_last]
  have ht := pwl_convex_telescope s (h r) N
  have hh0 : h r 0 = r := by simp only [hh, hg0, sub_zero]; exact max_eq_left hr
  rw [hh0] at ht
  simp only [hh] at ht
  simp only [hs, hg] at ht ⊢
  linarith
