-- Prove2me | solution 1 for TaylorRemainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:14:04.287357+00:00
-- url     : https://prove2.me/submissions/52291fc5-50fc-4985-b6d3-73d2308cfd74

import Definitions.Def_PHigherOrder_TaylorPoly
import Definitions.Def_PHigherOrder_IteratedDerivAlongRay
import Definitions.Def_PHigherOrder_TaylorRemainder
import Theorems.Thm_IteratedDerivAlongRay


set_option autoImplicit false
set_option linter.unusedVariables false
theorem _root_.solution (u : Plane → ℝ) (x₀ : Plane) (ρ : ℝ) (hρ : 0 < ρ)
    (k : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hu : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) u (Metric.ball x₀ ρ))
    (hbd : ∀ x ∈ Metric.ball x₀ ρ, ‖iteratedFDeriv ℝ (k + 1) u x‖ ≤ M) :
    ∀ x ∈ Metric.ball x₀ ρ,
      |u x - TaylorPoly k u x₀ x| ≤ M / (Nat.factorial (k + 1) : ℝ) * ‖x - x₀‖ ^ (k + 1) := by
  intro x hx
  set e : Plane := x - x₀ with he
  have heρ : ‖e‖ < ρ := by
    rw [he]; rw [Metric.mem_ball, dist_eq_norm] at hx; exact hx
  -- the ray and its parameter set
  set γ : ℝ → Plane := fun s => x₀ + s • e with hγ
  have hγC : ContDiff ℝ (⊤ : ℕ∞) γ := by
    rw [hγ]; exact contDiff_const.add (contDiff_id.smul contDiff_const)
  set J : Set ℝ := {s : ℝ | ‖s • e‖ < ρ} with hJ
  have hJopen : IsOpen J := isOpen_lt (by fun_prop) continuous_const
  have hmaps : ∀ s ∈ J, γ s ∈ Metric.ball x₀ ρ := by
    intro s hs
    rw [hγ]
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hs
  have hIccJ : Set.Icc (0:ℝ) 1 ⊆ J := by
    intro s hs
    have h0 : (0:ℝ) ≤ s := hs.1
    have hns : ‖s • e‖ = s * ‖e‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
    show ‖s • e‖ < ρ
    rw [hns]
    calc s * ‖e‖ ≤ 1 * ‖e‖ := by gcongr; exact hs.2
      _ = ‖e‖ := one_mul _
      _ < ρ := heρ
  set f : ℝ → ℝ := fun s => u (γ s) with hf
  have hfJ : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) f J :=
    hu.comp ((hγC.of_le (by exact_mod_cast le_top)).contDiffOn) (fun s hs => hmaps s hs)
  have huIcc : Set.uIcc (0:ℝ) 1 = Set.Icc (0:ℝ) 1 := Set.uIcc_of_le zero_le_one
  have huIoo : Set.uIoo (0:ℝ) 1 = Set.Ioo (0:ℝ) 1 := Set.uIoo_of_le zero_le_one
  have hUD : UniqueDiffOn ℝ (Set.Icc (0:ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hfIcc : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) f (Set.Icc (0:ℝ) 1) := hfJ.mono hIccJ
  -- Taylor-Lagrange on [0,1]
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin k f (Set.uIcc (0:ℝ) 1))
      (Set.uIoo (0:ℝ) 1) := by
    rw [huIcc, huIoo]
    exact (hfIcc.differentiableOn_iteratedDerivWithin
      (by exact_mod_cast Nat.lt_succ_self k) hUD).mono Set.Ioo_subset_Icc_self
  obtain ⟨s, hs, hEq⟩ := taylor_mean_remainder_lagrange (f := f) (x₀ := (0:ℝ)) (x := (1:ℝ))
    (n := k) (by norm_num) (by rw [huIcc]; exact hfIcc.of_le (by exact_mod_cast Nat.le_succ k))
    hdiff
  rw [huIoo] at hs
  -- identify f 1 and the Taylor sum
  have hf1 : f 1 = u x := by rw [hf, hγ]; simp [he]
  have hray : ∀ (j : ℕ) (t : ℝ), t ∈ J → j ≤ k + 1 →
      iteratedDeriv j f t = iteratedFDeriv ℝ j u (x₀ + t • e) (fun _ => e) := by
    intro j t htJ hjk
    exact IteratedDerivAlongRay (Metric.ball x₀ ρ) Metric.isOpen_ball u j
      (hu.of_le (by exact_mod_cast hjk)) x₀ e t (hmaps t htJ)
  have hTaylorSum : taylorWithinEval f k (Set.uIcc (0:ℝ) 1) 0 1 = TaylorPoly k u x₀ x := by
    rw [huIcc, taylor_within_apply, TaylorPoly]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjk : j ≤ k := Finset.mem_range_succ_iff.1 hj
    have h0J : (0:ℝ) ∈ J := hIccJ (Set.left_mem_Icc.2 zero_le_one)
    have hw : iteratedDerivWithin j f (Set.Icc (0:ℝ) 1) 0 = iteratedDeriv j f 0 :=
      iteratedDerivWithin_eq_iteratedDeriv hUD
        ((hfJ.contDiffAt (hJopen.mem_nhds h0J)).of_le (by exact_mod_cast Nat.le_succ_of_le hjk))
        (Set.left_mem_Icc.2 zero_le_one)
    rw [hw, hray j 0 h0J (Nat.le_succ_of_le hjk)]
    simp [he, smul_eq_mul]
  rw [hf1, hTaylorSum] at hEq
  -- bound the remainder
  have hsJ : s ∈ J := hIccJ (Set.Ioo_subset_Icc_self hs)
  have hwithin : iteratedDerivWithin (k + 1) f (Set.uIcc (0:ℝ) 1) s
      = iteratedFDeriv ℝ (k + 1) u (x₀ + s • e) (fun _ => e) := by
    rw [huIcc]
    rw [iteratedDerivWithin_eq_iteratedDeriv hUD
      (hfJ.contDiffAt (hJopen.mem_nhds hsJ)) (Set.Ioo_subset_Icc_self hs)]
    exact hray (k + 1) s hsJ le_rfl
  rw [hwithin] at hEq
  have hbdy : |iteratedFDeriv ℝ (k + 1) u (x₀ + s • e) (fun _ => e)| ≤ M * ‖e‖ ^ (k + 1) := by
    have h1 : |iteratedFDeriv ℝ (k + 1) u (x₀ + s • e) (fun _ => e)|
        ≤ ‖iteratedFDeriv ℝ (k + 1) u (x₀ + s • e)‖ * ∏ _i : Fin (k + 1), ‖e‖ := by
      simpa [Real.norm_eq_abs] using
        (iteratedFDeriv ℝ (k + 1) u (x₀ + s • e)).le_opNorm (fun _ => e)
    have h2 : (∏ _i : Fin (k + 1), ‖e‖) = ‖e‖ ^ (k + 1) := by simp
    rw [h2] at h1
    exact h1.trans (by gcongr; exact hbd _ (hmaps s hsJ))
  have hfac : (0:ℝ) < (Nat.factorial (k + 1) : ℝ) :=
    Nat.cast_pos.2 (Nat.factorial_pos (k + 1))
  rw [hEq]
  rw [he]
  rw [abs_div, abs_of_pos hfac]
  rw [div_le_iff₀ hfac]
  calc |iteratedFDeriv ℝ (k + 1) u (x₀ + s • e) (fun _ => e) * (1 - 0) ^ (k + 1)|
      = |iteratedFDeriv ℝ (k + 1) u (x₀ + s • e) (fun _ => e)| := by norm_num
    _ ≤ M * ‖e‖ ^ (k + 1) := hbdy
    _ = M / (Nat.factorial (k + 1) : ℝ) * ‖e‖ ^ (k + 1) * (Nat.factorial (k + 1) : ℝ) := by
        field_simp
