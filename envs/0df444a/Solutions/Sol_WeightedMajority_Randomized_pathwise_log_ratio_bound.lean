-- Prove2me | solution 1 for WeightedMajority.Randomized.pathwise_log_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-08T09:28:00.691627+00:00
-- url     : https://prove2.me/submissions/3754d348-56a0-4cc4-918b-47ecc6543e7b

import Mathlib
import Definitions.Def_WeightedMajority_Randomized_WMRModel
set_option autoImplicit false

open WeightedMajority.Randomized

-- Child B of the WeightedMajority theorem_6_1 decomposition (triage DECOMPOSE
-- 2026-10-07): pathwise log-ratio loss bound, pure real analysis.
-- Standalone proof: inlines child A (convex_abs_weighted_bound, ACCEPTED
-- 2026-10-08); no Theorems.Thm_* citations, no preamble helper redefinitions.
-- `theorem solution` is top-level (gate requirement); the published name is
-- provided as a type-ascribed alias inside the namespace below.
-- Proof idea: per trial, the (5.1)-upper bound in hM gives
--   s_{j+1} <= s_j * (1 - (1-beta)*|gamma^j - rho^j|)
-- via the convex-combination triangle inequality (child A); then
-- Real.log_le_sub_one_of_pos turns the multiplicative drop into the additive
-- per-trial bound (1-beta)*|gamma^j - rho^j| <= log (s_j / s_{j+1}), and the
-- drops telescope to log (s_0 / s_t).

theorem solution {Omega : Type*} [MeasurableSpace Omega] {n t : Nat}
    (beta : Real) (w1 : Fin n -> Real)
    (F : Nat -> Fin n -> Real -> Real -> Real)
    (x : Nat -> Fin n -> Omega -> Real)
    (rho lam : Nat -> Omega -> Real)
    (hM : IsWMRModel t beta w1 F x rho lam)
    (hpos : forall (j : Nat), j <= t ->
      forall (omega : Omega), 0 < totalWeight w1 F x rho j omega) :
    forall (omega : Omega), (1 - beta)
        * Finset.sum (Finset.range t)
            (fun j => abs (gamma w1 F x rho j omega - rho j omega))
      <= Real.log (totalWeight w1 F x rho 0 omega / totalWeight w1 F x rho t omega) := by
  obtain ⟨hβ0, hβ1, hw1pos, -, -, hx01, -, -, -, -, hF⟩ := hM
  intro ω
  have hL : 0 ≤ 1 - beta := by linarith
  -- Child A, inlined verbatim from the ACCEPTED standalone proof:
  -- convex-combination triangle inequality.
  have hchildA : ∀ {m : Nat} (w x : Fin m → ℝ) (rho : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
      (0 < Finset.sum Finset.univ (fun i => w i)) →
      abs (Finset.sum Finset.univ (fun i => w i * x i)
        / Finset.sum Finset.univ (fun i => w i) - rho)
        * Finset.sum Finset.univ (fun i => w i)
        ≤ Finset.sum Finset.univ (fun i => w i * abs (x i - rho)) := by
    intro m w x rho hw hx hS
    have hSne : Finset.sum Finset.univ (fun i => w i) ≠ 0 := ne_of_gt hS
    have habsS : abs (Finset.sum Finset.univ (fun i => w i))
        = Finset.sum Finset.univ (fun i => w i) := abs_of_pos hS
    have h1 : Finset.sum Finset.univ (fun i => w i * (x i - rho))
        = Finset.sum Finset.univ (fun i => w i * x i)
          - rho * Finset.sum Finset.univ (fun i => w i) := by
      have e : ∀ i ∈ Finset.univ, w i * (x i - rho) = w i * x i - w i * rho :=
        fun i _ => mul_sub _ _ _
      rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib,
        ← Finset.sum_mul Finset.univ (fun x => w x) rho, mul_comm rho]
    have hfrac : Finset.sum Finset.univ (fun i => w i * x i)
          / Finset.sum Finset.univ (fun i => w i) - rho
        = Finset.sum Finset.univ (fun i => w i * (x i - rho))
          / Finset.sum Finset.univ (fun i => w i) := by
      rw [eq_div_iff hSne, sub_mul, div_mul_cancel₀ _ hSne, h1]
    have hstep : abs (Finset.sum Finset.univ (fun i => w i * x i)
          / Finset.sum Finset.univ (fun i => w i) - rho)
          * Finset.sum Finset.univ (fun i => w i)
        = abs (Finset.sum Finset.univ (fun i => w i * (x i - rho))) := by
      rw [hfrac, abs_div, habsS, div_mul_cancel₀ _ hSne]
    rw [hstep]
    calc abs (Finset.sum Finset.univ (fun i => w i * (x i - rho)))
        ≤ Finset.sum Finset.univ (fun i => abs (w i * (x i - rho))) :=
          Finset.abs_sum_le_sum_abs _ _
      _ = Finset.sum Finset.univ (fun i => w i * abs (x i - rho)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul, abs_of_nonneg (hw i)]
  -- Weights stay nonnegative along the path (F ≥ β^|·| ≥ 0 on trials j < t).
  have hwnonneg : ∀ j, j ≤ t → ∀ i, 0 ≤ weight w1 F x rho j i ω := by
    intro j
    induction j with
    | zero =>
      intro _ i
      show 0 ≤ w1 i
      exact le_of_lt (hw1pos i)
    | succ k ih =>
      intro hle i
      have hkt : k < t := Nat.lt_of_succ_le hle
      have hkle : k ≤ t := Nat.le_of_succ_le hle
      have hFnn : 0 ≤ F k i (x k i ω) (rho k ω) :=
        le_trans (Real.rpow_nonneg hβ0 _) (hF k hkt i ω).1
      show 0 ≤ F k i (x k i ω) (rho k ω) * weight w1 F x rho k i ω
      exact mul_nonneg hFnn (ih hkle i)
  -- Per trial: s_{j+1} ≤ s_j - (1-β) * Σ_i w_{j,i} |x_{j,i} - rho_j|.
  have hstep : ∀ j, j < t →
      totalWeight w1 F x rho (j + 1) ω
        ≤ totalWeight w1 F x rho j ω
          - (1 - beta) * ∑ i : Fin n, weight w1 F x rho j i ω * abs (x j i ω - rho j ω) := by
    intro j hjt
    have e0 : totalWeight w1 F x rho (j + 1) ω
        = ∑ i : Fin n, F j i (x j i ω) (rho j ω) * weight w1 F x rho j i ω := rfl
    rw [e0]
    have hterm : ∀ i : Fin n, F j i (x j i ω) (rho j ω) * weight w1 F x rho j i ω
        ≤ (1 - (1 - beta) * abs (x j i ω - rho j ω)) * weight w1 F x rho j i ω :=
      fun i => mul_le_mul_of_nonneg_right (hF j hjt i ω).2 (hwnonneg j (le_of_lt hjt) i)
    have hsplit : ∀ i : Fin n,
        (1 - (1 - beta) * abs (x j i ω - rho j ω)) * weight w1 F x rho j i ω
        = weight w1 F x rho j i ω
          - (1 - beta) * (weight w1 F x rho j i ω * abs (x j i ω - rho j ω)) := by
      intro i; ring
    calc ∑ i : Fin n, F j i (x j i ω) (rho j ω) * weight w1 F x rho j i ω
        ≤ ∑ i : Fin n, (1 - (1 - beta) * abs (x j i ω - rho j ω)) * weight w1 F x rho j i ω :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = ∑ i : Fin n, weight w1 F x rho j i ω
            - (1 - beta) * ∑ i : Fin n, weight w1 F x rho j i ω * abs (x j i ω - rho j ω) := by
          simp_rw [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = totalWeight w1 F x rho j ω
            - (1 - beta) * ∑ i : Fin n, weight w1 F x rho j i ω * abs (x j i ω - rho j ω) := rfl
  -- Multiplicative drop: s_{j+1} ≤ s_j * (1 - (1-β)|γ^j - rho^j|), via child A.
  have hdrop : ∀ j, j < t →
      totalWeight w1 F x rho (j + 1) ω
        ≤ totalWeight w1 F x rho j ω
          * (1 - (1 - beta) * abs (gamma w1 F x rho j ω - rho j ω)) := by
    intro j hjt
    have h1 := hstep j hjt
    have h2 := hchildA (fun i => weight w1 F x rho j i ω) (fun i => x j i ω) (rho j ω)
      (fun i => hwnonneg j (le_of_lt hjt) i) (fun i => hx01 j hjt i ω)
      (hpos j (le_of_lt hjt) ω)
    have h3 : (1 - beta) * (abs (gamma w1 F x rho j ω - rho j ω) * totalWeight w1 F x rho j ω)
        ≤ (1 - beta) * ∑ i : Fin n, weight w1 F x rho j i ω * abs (x j i ω - rho j ω) :=
      mul_le_mul_of_nonneg_left h2 hL
    calc totalWeight w1 F x rho (j + 1) ω
        ≤ totalWeight w1 F x rho j ω
            - (1 - beta) * ∑ i : Fin n, weight w1 F x rho j i ω * abs (x j i ω - rho j ω) := h1
      _ ≤ totalWeight w1 F x rho j ω
            - (1 - beta) * (abs (gamma w1 F x rho j ω - rho j ω) * totalWeight w1 F x rho j ω) :=
          sub_le_sub_left h3 _
      _ = totalWeight w1 F x rho j ω
            * (1 - (1 - beta) * abs (gamma w1 F x rho j ω - rho j ω)) := by ring
  -- The ratio s_{j+1}/s_j lower-bounds (1 - (1-β)|γ^j - rho^j|), which is positive.
  have hratio_le : ∀ j, j < t →
      totalWeight w1 F x rho (j + 1) ω / totalWeight w1 F x rho j ω
        ≤ 1 - (1 - beta) * abs (gamma w1 F x rho j ω - rho j ω) := by
    intro j hjt
    have hsj : 0 < totalWeight w1 F x rho j ω := hpos j (le_of_lt hjt) ω
    have hd := hdrop j hjt
    rw [div_le_iff₀ hsj]
    calc totalWeight w1 F x rho (j + 1) ω
        ≤ totalWeight w1 F x rho j ω
          * (1 - (1 - beta) * abs (gamma w1 F x rho j ω - rho j ω)) := hd
      _ = (1 - (1 - beta) * abs (gamma w1 F x rho j ω - rho j ω))
          * totalWeight w1 F x rho j ω := by rw [mul_comm]
  have hratio_pos : ∀ j, j < t →
      0 < 1 - (1 - beta) * abs (gamma w1 F x rho j ω - rho j ω) := by
    intro j hjt
    have hsj : 0 < totalWeight w1 F x rho j ω := hpos j (le_of_lt hjt) ω
    have hsj1 : 0 < totalWeight w1 F x rho (j + 1) ω := hpos (j + 1) hjt ω
    have hle := hratio_le j hjt
    have hposr : 0 < totalWeight w1 F x rho (j + 1) ω / totalWeight w1 F x rho j ω :=
      div_pos hsj1 hsj
    linarith
  -- Per-trial additive bound: (1-β)|γ^j - rho^j| ≤ log(s_j/s_{j+1}).
  have hlogstep : ∀ j, j < t →
      (1 - beta) * abs (gamma w1 F x rho j ω - rho j ω)
        ≤ Real.log (totalWeight w1 F x rho j ω / totalWeight w1 F x rho (j + 1) ω) := by
    intro j hjt
    have hsj : 0 < totalWeight w1 F x rho j ω := hpos j (le_of_lt hjt) ω
    have hsj1 : 0 < totalWeight w1 F x rho (j + 1) ω := hpos (j + 1) hjt ω
    have hrz : 0 < 1 - (1 - beta) * abs (gamma w1 F x rho j ω - rho j ω) := hratio_pos j hjt
    have hle := hratio_le j hjt
    have hlog1 : Real.log (totalWeight w1 F x rho (j + 1) ω / totalWeight w1 F x rho j ω)
        ≤ Real.log (1 - (1 - beta) * abs (gamma w1 F x rho j ω - rho j ω)) :=
      Real.log_le_log (div_pos hsj1 hsj) hle
    have hlog2 : Real.log (1 - (1 - beta) * abs (gamma w1 F x rho j ω - rho j ω))
        ≤ (1 - (1 - beta) * abs (gamma w1 F x rho j ω - rho j ω)) - 1 :=
      Real.log_le_sub_one_of_pos hrz
    have hdecomp : Real.log (totalWeight w1 F x rho j ω / totalWeight w1 F x rho (j + 1) ω)
        = -Real.log (totalWeight w1 F x rho (j + 1) ω / totalWeight w1 F x rho j ω) := by
      rw [Real.log_div (ne_of_gt hsj1) (ne_of_gt hsj),
        Real.log_div (ne_of_gt hsj) (ne_of_gt hsj1)]
      ring
    rw [hdecomp]
    linarith
  -- Sum the per-trial bounds and telescope.
  have hs0 : 0 < totalWeight w1 F x rho 0 ω := hpos 0 (Nat.zero_le t) ω
  have hst : 0 < totalWeight w1 F x rho t ω := hpos t le_rfl ω
  rw [Finset.mul_sum]
  calc ∑ j ∈ Finset.range t, (1 - beta) * abs (gamma w1 F x rho j ω - rho j ω)
      ≤ ∑ j ∈ Finset.range t,
          Real.log (totalWeight w1 F x rho j ω / totalWeight w1 F x rho (j + 1) ω) :=
        Finset.sum_le_sum (fun j hj => hlogstep j (Finset.mem_range.mp hj))
    _ = Real.log (totalWeight w1 F x rho 0 ω / totalWeight w1 F x rho t ω) := by
        have htel : ∀ j ∈ Finset.range t,
            Real.log (totalWeight w1 F x rho j ω / totalWeight w1 F x rho (j + 1) ω)
              = Real.log (totalWeight w1 F x rho j ω)
                - Real.log (totalWeight w1 F x rho (j + 1) ω) := by
          intro j hj
          have hjt : j < t := Finset.mem_range.mp hj
          rw [Real.log_div (ne_of_gt (hpos j (le_of_lt hjt) ω))
            (ne_of_gt (hpos (j + 1) hjt ω))]
        rw [Finset.sum_congr rfl htel,
          Finset.sum_range_sub' (fun j => Real.log (totalWeight w1 F x rho j ω)),
          Real.log_div (ne_of_gt hs0) (ne_of_gt hst)]

namespace WeightedMajority.Randomized

theorem pathwise_log_ratio_bound {Omega : Type*} [MeasurableSpace Omega] {n t : Nat}
    (beta : Real) (w1 : Fin n -> Real)
    (F : Nat -> Fin n -> Real -> Real -> Real)
    (x : Nat -> Fin n -> Omega -> Real)
    (rho lam : Nat -> Omega -> Real)
    (hM : IsWMRModel t beta w1 F x rho lam)
    (hpos : forall (j : Nat), j <= t ->
      forall (omega : Omega), 0 < totalWeight w1 F x rho j omega) :
    forall (omega : Omega), (1 - beta)
        * Finset.sum (Finset.range t)
            (fun j => abs (gamma w1 F x rho j omega - rho j omega))
      <= Real.log (totalWeight w1 F x rho 0 omega / totalWeight w1 F x rho t omega) :=
  solution beta w1 F x rho lam hM hpos

end WeightedMajority.Randomized
