-- Prove2me | solution 1 for Plasticity.A01_quant
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T17:57:13.762791+00:00
-- url     : https://prove2.me/submissions/6d5b12d8-1be6-4c58-92f0-efe6db334504

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_A01
import Theorems.Thm_Plasticity_A01_averaged_covers
import Theorems.Thm_Plasticity_Ext_KMRate

namespace Sol_Plasticity_A01_quant

open Metric

/-- The stability estimate (2.7) of `conjugated_contractions.md` for a fixed number `n ≥ 1` of
steps: with `K = H / (1 + ε)` and `P = (7/8) I + (1/8) K`, every point of the ball is within
`n d / 8` of `Pⁿ(B)`, where `d = 1 - (1 + ε)⁻¹`, and the Baillon–Bruck rate controls
`‖Pⁿ v - K (Pⁿ v)‖`. -/
theorem stability {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (ε : ℝ) (hε : 0 ≤ ε) (H : X → X)
    (hmaps : Set.MapsTo H (closedBall (0 : X) 1) (closedBall (0 : X) 1))
    (hlip : ∀ x ∈ closedBall (0 : X) 1, ∀ y ∈ closedBall (0 : X) 1,
      ‖H x - H y‖ ≤ (1 + ε) * ‖x - y‖)
    (halign : ∀ a ∈ sphere (0 : X) 1, ‖a + H a‖ = 2)
    (n : ℕ) (hn : 1 ≤ n) (z : X) (hz : z ∈ closedBall (0 : X) 1) :
    ‖H z - z‖ ≤ (1 - (1 + ε)⁻¹) * (1 + n / 4)
      + 2 / Real.sqrt (Real.pi * n * (1 / 8) * (1 - 1 / 8)) := by
  set B := closedBall (0 : X) 1 with hB
  have hnormB : ∀ x, x ∈ B ↔ ‖x‖ ≤ 1 := fun x => by simp [hB]
  set L : ℝ := 1 + ε with hL
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hLinv : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL1
  have hLinv0 : 0 < L⁻¹ := inv_pos.mpr hLpos
  set d : ℝ := 1 - L⁻¹ with hd
  have hd0 : 0 ≤ d := by linarith
  have hd1 : d < 1 := by linarith
  set α : ℝ := 1 / 8 with hα
  have hα0 : 0 < α := by norm_num [hα]
  set K : X → X := fun x => L⁻¹ • H x with hK
  -- `K` is a nonexpansive self-map of the ball.
  have hKmaps : Set.MapsTo K B B := by
    intro x hx
    have hHx := (hnormB _).1 (hmaps hx)
    rw [hnormB]
    simp only [hK, norm_smul, Real.norm_eq_abs, abs_of_pos hLinv0]
    calc L⁻¹ * ‖H x‖ ≤ 1 * 1 := mul_le_mul hLinv hHx (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hKlip' : ∀ x ∈ B, ∀ y ∈ B, ‖K x - K y‖ ≤ ‖x - y‖ := by
    intro x hx y hy
    simp only [hK, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hLinv0]
    calc L⁻¹ * ‖H x - H y‖ ≤ L⁻¹ * (L * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (hlip x hx y hy) hLinv0.le
      _ = ‖x - y‖ := by field_simp
  have hKlip : LipschitzOnWith 1 K B := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa [dist_eq_norm] using hKlip' x hx y hy
  -- On the sphere the averaged map loses at most `α d` of norm: a norming functional of
  -- `a + H a` takes the value `1` at `a` and at `H a`.
  have hPa : ∀ a ∈ sphere (0 : X) 1, 1 - α * d ≤ ‖(1 - α) • a + α • K a‖ := by
    intro a ha
    have ha1 : ‖a‖ = 1 := by simpa using ha
    have hne : ‖a + H a‖ ≠ 0 := by rw [halign a ha]; norm_num
    obtain ⟨g, hg1, hga⟩ := exists_dual_vector ℝ (a + H a) hne
    have h1 : g a ≤ 1 := by
      have := g.le_opNorm a
      rw [hg1, ha1, Real.norm_eq_abs] at this
      linarith [le_abs_self (g a)]
    have h2 : g (H a) ≤ 1 := by
      have := g.le_opNorm (H a)
      have hHa : ‖H a‖ ≤ 1 := (hnormB _).1 (hmaps (sphere_subset_closedBall ha))
      rw [hg1, Real.norm_eq_abs] at this
      linarith [le_abs_self (g (H a))]
    have hsum : g a + g (H a) = 2 := by rw [← map_add, hga, halign a ha]; norm_num
    have hga1 : g a = 1 := by linarith
    have hgHa1 : g (H a) = 1 := by linarith
    have hval : g ((1 - α) • a + α • K a) = 1 - α * d := by
      simp only [hK, map_add, map_smul, smul_eq_mul, hga1, hgHa1, hd]
      ring
    have := g.le_opNorm ((1 - α) • a + α • K a)
    rw [hg1, one_mul, hval, Real.norm_eq_abs] at this
    linarith [le_abs_self (1 - α * d)]
  -- Hence `P` covers the ball of radius `1 - α d`.
  have hP_cover : ∀ y : X, ‖y‖ ≤ 1 - α * d → ∃ x ∈ B, (1 - α) • x + α • K x = y := by
    intro y hy
    exact Plasticity.A01.averaged_covers K hKmaps hKlip α (α * d) hα0 (by norm_num [hα])
      (by positivity) (by rw [hα]; linarith) hPa y hy
  set P : X → X := fun z => (1 - α) • z + α • K z with hP
  have hPmaps : Set.MapsTo P B B := by
    intro x hx
    exact (convex_closedBall (0 : X) 1) hx (hKmaps hx) (by norm_num [hα]) (by norm_num [hα])
      (by ring)
  have hPlip : ∀ x ∈ B, ∀ y ∈ B, ‖P x - P y‖ ≤ ‖x - y‖ := by
    intro x hx y hy
    have e : P x - P y = (1 - α) • (x - y) + α • (K x - K y) := by simp only [hP]; module
    rw [e]
    have h1α : 0 < 1 - α := by norm_num [hα]
    calc _ ≤ ‖(1 - α) • (x - y)‖ + ‖α • (K x - K y)‖ := norm_add_le _ _
      _ = (1 - α) * ‖x - y‖ + α * ‖K x - K y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h1α,
            abs_of_pos hα0]
      _ ≤ (1 - α) * ‖x - y‖ + α * ‖x - y‖ := by
          gcongr
          exact hKlip' x hx y hy
      _ = ‖x - y‖ := by ring
  -- (2.4): every point of the ball is within `m α d` of `P^m(B)`.
  have happrox : ∀ m : ℕ, ∀ z ∈ B, ∃ v ∈ B, ‖z - P^[m] v‖ ≤ m * (α * d) := by
    intro m
    induction m with
    | zero => intro z hz; exact ⟨z, hz, by simp⟩
    | succ m ih =>
      intro z hz
      have hz1 : ‖z‖ ≤ 1 := (hnormB z).1 hz
      have hαd : 0 ≤ α * d := by positivity
      have hαd1 : α * d ≤ 1 := by rw [hα]; linarith
      have hy1 : ‖(1 - α * d) • z‖ ≤ 1 - α * d := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        calc (1 - α * d) * ‖z‖ ≤ (1 - α * d) * 1 := mul_le_mul_of_nonneg_left hz1 (by linarith)
          _ = 1 - α * d := mul_one _
      have hzy : ‖z - (1 - α * d) • z‖ ≤ α * d := by
        have e : z - (1 - α * d) • z = (α * d) • z := by module
        rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hαd]
        calc α * d * ‖z‖ ≤ α * d * 1 := mul_le_mul_of_nonneg_left hz1 hαd
          _ = α * d := mul_one _
      obtain ⟨w, hw, hPw⟩ := hP_cover _ hy1
      obtain ⟨v, hv, hwv⟩ := ih w hw
      refine ⟨v, hv, ?_⟩
      have hPnv : P^[m] v ∈ B := (hPmaps.iterate m) hv
      have hPw' : P w = (1 - α * d) • z := hPw
      rw [Function.iterate_succ_apply']
      calc ‖z - P (P^[m] v)‖
          ≤ ‖z - (1 - α * d) • z‖ + ‖(1 - α * d) • z - P (P^[m] v)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ α * d + ‖w - P^[m] v‖ := by
            gcongr
            rw [← hPw']
            exact hPlip w hw _ hPnv
        _ ≤ α * d + m * (α * d) := by gcongr
        _ = ((m + 1 : ℕ) : ℝ) * (α * d) := by push_cast; ring
  -- Approximate `z` by a point `u = Pⁿ v` and apply the Baillon–Bruck rate at `u`.
  obtain ⟨v, hv, hzv⟩ := happrox n z hz
  have hdiam : ∀ x ∈ B, ∀ y ∈ B, ‖x - y‖ ≤ 2 := by
    intro x hx y hy
    have := norm_sub_le x y
    linarith [(hnormB x).1 hx, (hnormB y).1 hy]
  have hrate := Plasticity.Ext.KMRate B (convex_closedBall 0 1) 2 hdiam K hKmaps hKlip α hα0
    (by norm_num [hα]) n hn v hv
  set u := P^[n] v with hu
  change ‖u - K u‖ ≤ _ at hrate
  have hu_mem : u ∈ B := (hPmaps.iterate n) hv
  have hHK : ‖H z - K z‖ ≤ d := by
    have e : H z - K z = d • H z := by simp only [hK, hd]; module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hd0]
    calc d * ‖H z‖ ≤ d * 1 := mul_le_mul_of_nonneg_left ((hnormB _).1 (hmaps hz)) hd0
      _ = d := mul_one d
  have hKzu : ‖K z - K u‖ ≤ ‖z - u‖ := hKlip' z hz u hu_mem
  have e : H z - z = ((H z - K z) + (K z - K u)) + ((K u - u) + (u - z)) := by abel
  have t1 := norm_add_le ((H z - K z) + (K z - K u)) ((K u - u) + (u - z))
  have t2 := norm_add_le (H z - K z) (K z - K u)
  have t3 := norm_add_le (K u - u) (u - z)
  have t4 : ‖u - z‖ = ‖z - u‖ := norm_sub_rev u z
  have t5 : ‖K u - u‖ = ‖u - K u‖ := norm_sub_rev (K u) u
  rw [e]
  have hαval : α = 1 / 8 := hα
  rw [hαval] at hzv
  linarith

end Sol_Plasticity_A01_quant

theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (ε : NNReal) (H : X → X)
    (hmaps : Set.MapsTo H (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : X) 1))
    (hlip : LipschitzOnWith (1 + ε) H (Metric.closedBall (0 : X) 1))
    (halign : ∀ a ∈ Metric.sphere (0 : X) 1, ‖a + H a‖ = 2) :
    ∀ x ∈ Metric.closedBall (0 : X) 1, ‖H x - x‖ ≤ min 2 (4 * (ε : ℝ) ^ ((1 : ℝ) / 3)) := by
  intro x hx
  have hε0 : (0 : ℝ) ≤ ε := ε.2
  set t : ℝ := (ε : ℝ) ^ ((1 : ℝ) / 3) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hε0 _
  have ht3 : t ^ 3 = ε := by
    have h := Real.rpow_inv_natCast_pow (x := (ε : ℝ)) hε0 (show (3 : ℕ) ≠ 0 by norm_num)
    rw [ht, one_div]
    simpa using h
  have hx1 : ‖x‖ ≤ 1 := by simpa using hx
  have hHx1 : ‖H x‖ ≤ 1 := by simpa using hmaps hx
  have hdist2 : ‖H x - x‖ ≤ 2 := by
    have := norm_sub_le (H x) x
    linarith
  refine le_min hdist2 ?_
  by_cases hbig : 1 / 2 ≤ t
  · linarith
  rw [not_le] at hbig
  rcases eq_or_ne ε 0 with h0 | h0
  · subst h0
    have hlip1 : LipschitzOnWith 1 H (Metric.closedBall (0 : X) 1) := by simpa using hlip
    have hHx : H x = x := Plasticity.A01 H hmaps hlip1 halign hx
    rw [hHx, sub_self, norm_zero]
    positivity
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr h0)
  have htpos : 0 < t := Real.rpow_pos_of_pos hεpos _
  set n : ℕ := ⌈4 / t ^ 2⌉₊ with hn
  have hn_ge : 4 / t ^ 2 ≤ n := Nat.le_ceil _
  have hn_lt : (n : ℝ) < 4 / t ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hn1 : 1 ≤ n := by
    have h : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn_ge
    exact_mod_cast h
  have hlipR : ∀ x ∈ Metric.closedBall (0 : X) 1, ∀ y ∈ Metric.closedBall (0 : X) 1,
      ‖H x - H y‖ ≤ (1 + (ε : ℝ)) * ‖x - y‖ := by
    intro x hx y hy
    have := hlip.dist_le_mul x hx y hy
    simpa [dist_eq_norm] using this
  have hmain := Sol_Plasticity_A01_quant.stability (ε : ℝ) hε0 H hmaps hlipR halign n hn1 x hx
  -- `d = ε / (1 + ε) ≤ ε`.
  have hd : 1 - (1 + (ε : ℝ))⁻¹ ≤ ε := by
    have hpos : (0 : ℝ) < 1 + ε := by linarith
    have hw := mul_inv_cancel₀ (ne_of_gt hpos)
    have hw0 := inv_pos.mpr hpos
    nlinarith [mul_nonneg hw0.le hε0]
  -- The rate term is at most `(7/4) t` because `t² n ≥ 4` and `π > 3`.
  have htn : 4 ≤ t ^ 2 * n := by
    have := hn_ge
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hrate : 2 / Real.sqrt (Real.pi * n * (1 / 8) * (1 - 1 / 8)) ≤ 7 / 4 * t := by
    have hQ0 : 0 < Real.pi * n * (1 / 8) * (1 - 1 / 8) := by
      have : (0 : ℝ) < n := by exact_mod_cast hn1
      have := Real.pi_pos
      positivity
    set s := Real.sqrt (Real.pi * n * (1 / 8) * (1 - 1 / 8)) with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr hQ0
    have hs2 : s ^ 2 = Real.pi * n * (1 / 8) * (1 - 1 / 8) := Real.sq_sqrt hQ0.le
    have h12 : 12 ≤ Real.pi * (t ^ 2 * n) := by nlinarith [Real.pi_gt_three]
    have hsq : 4 < (7 / 4 * t * s) ^ 2 := by
      have : (7 / 4 * t * s) ^ 2 = 49 / 16 * (7 / 64) * (Real.pi * (t ^ 2 * n)) := by
        rw [mul_pow, hs2]; ring
      rw [this]
      linarith
    have hx0 : 0 ≤ 7 / 4 * t * s := by positivity
    rw [div_le_iff₀ hs0]
    nlinarith
  have hdn : (1 - (1 + (ε : ℝ))⁻¹) * (1 + n / 4) ≤ t ^ 3 * (1 + n / 4) :=
    mul_le_mul_of_nonneg_right (by rw [ht3]; exact hd) (by positivity)
  have hn' : t ^ 2 * (n : ℝ) ≤ 4 + t ^ 2 := by
    have := hn_lt
    have h4 : 4 / t ^ 2 * t ^ 2 = 4 := div_mul_cancel₀ _ (by positivity)
    nlinarith [sq_nonneg t]
  have ht3n : t ^ 3 * (n : ℝ) ≤ t * (4 + t ^ 2) := by
    have : t ^ 3 * (n : ℝ) = t * (t ^ 2 * n) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hn' ht0
  have ht3t : t ^ 3 ≤ t := by nlinarith
  nlinarith
