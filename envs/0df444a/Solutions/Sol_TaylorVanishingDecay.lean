-- Prove2me | solution 1 for TaylorVanishingDecay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:14:58.229798+00:00
-- url     : https://prove2.me/submissions/aa05ad44-ade8-46b3-82de-ddb34c9efa1d

import Definitions.Def_PHigherOrder_IteratedDerivAlongRay
import Definitions.Def_PHigherOrder_TaylorVanishingDecay
import Theorems.Thm_IteratedDerivAlongRay


set_option autoImplicit false

theorem _root_.solution (u : Plane → ℝ) (x₀ : Plane) (ρ : ℝ) (hρ : 0 < ρ)
    (k : ℕ) (hk : 1 ≤ k) (β : ℝ) (hβ : 0 < β) (C : ℝ) (hC : 0 ≤ C)
    (hu : ContDiffOn ℝ (k : ℕ∞) u (Metric.ball x₀ ρ))
    (hvanish : ∀ j ≤ k, ∀ w : Plane, iteratedFDeriv ℝ j u x₀ (fun _ => w) = 0)
    (hhold : ∀ x ∈ Metric.ball x₀ ρ, ∀ y ∈ Metric.ball x₀ ρ,
        ‖iteratedFDeriv ℝ k u x - iteratedFDeriv ℝ k u y‖ ≤ C * ‖x - y‖ ^ β) :
    ∀ x ∈ Metric.ball x₀ ρ,
      |u x| ≤ C / (Nat.factorial k : ℝ) * ‖x - x₀‖ ^ ((k : ℝ) + β) := by
  have hfacpos : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hkb : (0 : ℝ) < (k : ℝ) + β := by
    have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  -- Hypothesis (2) at order `0`:  the `0`-th derivative IS the value, so `u` vanishes at `x₀`.
  have hu0 : u x₀ = 0 := by
    have h := hvanish 0 (Nat.zero_le k) 0
    rwa [iteratedFDeriv_zero_apply] at h
  intro x hx
  -- Name the displacement opaquely, so the two cases are a dichotomy on `‖e‖`.
  obtain ⟨e, hedef⟩ : ∃ e : Plane, x - x₀ = e := ⟨x - x₀, rfl⟩
  rw [hedef]
  have hxe : x = x₀ + e := by rw [← hedef]; abel
  have hnelt : ‖e‖ < ρ := by rw [← hedef, ← dist_eq_norm]; exact hx
  -- Every parameter in `[-1,1]` keeps the ray inside the ball, since `‖e‖ < ρ`.
  have hmem : ∀ s : ℝ, |s| ≤ 1 → x₀ + s • e ∈ Metric.ball x₀ ρ := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |s| * ‖e‖ ≤ 1 * ‖e‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg e)
      _ = ‖e‖ := one_mul _
      _ < ρ := hnelt
  rcases eq_or_lt_of_le (norm_nonneg e) with hz | hepos
  · -- Case 1:  `x = x₀`.  Both sides are zero, the right one because `k + β > 0`.
    have he0 : e = 0 := norm_eq_zero.mp hz.symm
    have hxx : x = x₀ := by rw [hxe, he0, add_zero]
    rw [hxx, hu0, abs_zero, ← hz, Real.zero_rpow (ne_of_gt hkb), mul_zero]
  · -- Case 2:  `0 < ‖e‖ < ρ`, so the ray argument and the real powers are available.
    -- Step 1: the restriction to the ray is `C^k` on the open preimage of the ball.
    have hγ : ContDiff ℝ (k : ℕ∞) (fun s : ℝ => x₀ + s • e) :=
      contDiff_const.add (contDiff_id.smul contDiff_const)
    have hJopen : IsOpen ((fun s : ℝ => x₀ + s • e) ⁻¹' Metric.ball x₀ ρ) :=
      Metric.isOpen_ball.preimage (by fun_prop)
    have hphiJ : ContDiffOn ℝ (k : ℕ∞) (fun s : ℝ => u (x₀ + s • e))
        ((fun s : ℝ => x₀ + s • e) ⁻¹' Metric.ball x₀ ρ) :=
      hu.comp hγ.contDiffOn fun s hs => hs
    have h0J : (0 : ℝ) ∈ (fun s : ℝ => x₀ + s • e) ⁻¹' Metric.ball x₀ ρ := by
      show x₀ + (0 : ℝ) • e ∈ Metric.ball x₀ ρ
      simp only [zero_smul, add_zero]
      exact Metric.mem_ball_self hρ
    have hphiAt : ContDiffAt ℝ (k : ℕ∞) (fun s : ℝ => u (x₀ + s • e)) 0 :=
      hphiJ.contDiffAt (hJopen.mem_nhds h0J)
    have hsubJ : Set.uIcc (0 : ℝ) 1 ⊆ (fun s : ℝ => x₀ + s • e) ⁻¹' Metric.ball x₀ ρ := by
      intro s hs
      rw [Set.uIcc_of_le zero_le_one] at hs
      show x₀ + s • e ∈ Metric.ball x₀ ρ
      exact hmem s (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩)
    -- Step 2: the ray lemma, at every order up to `k` and every admissible parameter.
    have hray : ∀ j : ℕ, j ≤ k → ∀ t : ℝ, |t| ≤ 1 →
        iteratedDeriv j (fun s : ℝ => u (x₀ + s • e)) t
          = iteratedFDeriv ℝ j u (x₀ + t • e) (fun _ => e) := fun j hj t ht =>
      IteratedDerivAlongRay (Metric.ball x₀ ρ) Metric.isOpen_ball u j
        (hu.of_le (by exact_mod_cast hj)) x₀ e t (hmem t ht)
    have hk1 : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk
    -- Step 3a: the degree-`(k-1)` Taylor polynomial at `0` collapses to `0`, every term
    -- being killed by hypothesis (2) transported along the ray.
    have hpoly : taylorWithinEval (fun s : ℝ => u (x₀ + s • e)) (k - 1) (Set.uIcc 0 1) 0 1
        = 0 := by
      rw [taylor_within_apply]
      refine Finset.sum_eq_zero ?_
      intro j hj
      have hjk : j < k := by have := Finset.mem_range.mp hj; omega
      have hzero : iteratedDerivWithin j (fun s : ℝ => u (x₀ + s • e)) (Set.uIcc 0 1) 0 = 0 := by
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num))
            (hphiAt.of_le (by exact_mod_cast hjk.le)) Set.left_mem_uIcc,
          hray j hjk.le 0 (by norm_num)]
        simpa using hvanish j hjk.le e
      rw [hzero, smul_zero]
    -- Step 3b: Taylor with Lagrange remainder on `[0,1]`, in the plain `iteratedDeriv` form.
    obtain ⟨xi, hxi, hTay⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (f := fun s : ℝ => u (x₀ + s • e))
        (x₀ := (0 : ℝ)) (x := (1 : ℝ)) (n := k - 1) (by norm_num)
        ((hphiJ.mono hsubJ).of_le
          (by
            -- `(k - 1) + 1` and `k` agree, but the cast into `WithTop ℕ∞` does not
            -- normalise, so rewrite with `hk1` after `norm_cast`.
            norm_cast
            rw [hk1]))
    rw [Set.uIoo_of_lt zero_lt_one, Set.mem_Ioo] at hxi
    rw [hpoly, hk1] at hTay
    simp only [sub_zero, one_pow, mul_one, one_smul] at hTay
    have hximem : |xi| ≤ 1 := abs_le.mpr ⟨by linarith [hxi.1], hxi.2.le⟩
    rw [hray k le_rfl xi hximem] at hTay
    have hux : u x = u (x₀ + e) := by rw [hxe]
    -- Step 4a: `D^k u x₀` kills the diagonal, so the remainder is a DIFFERENCE of forms
    -- evaluated at the fixed family -- the subtraction happens before evaluation.
    have hdiag : iteratedFDeriv ℝ k u (x₀ + xi • e) (fun _ => e)
        = (iteratedFDeriv ℝ k u (x₀ + xi • e) - iteratedFDeriv ℝ k u x₀)
            (fun _ : Fin k => e) := by
      rw [sub_apply, hvanish k le_rfl e, sub_zero]
    -- Step 4b: the operator norm against the diagonal family.
    have hnorme : ‖(fun _ : Fin k => e)‖ ≤ ‖e‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg e)).mpr fun _ => le_rfl
    have hopn : ‖(iteratedFDeriv ℝ k u (x₀ + xi • e) - iteratedFDeriv ℝ k u x₀)
        (fun _ : Fin k => e)‖
        ≤ ‖iteratedFDeriv ℝ k u (x₀ + xi • e) - iteratedFDeriv ℝ k u x₀‖ * ‖e‖ ^ k :=
      ContinuousMultilinearMap.le_opNorm_mul_pow_of_le _ hnorme
    -- Step 4c: hypothesis (3) on the pair `(x₀ + ξ e, x₀)`, then `ξ ^ β ≤ 1`.
    have hholder : ‖iteratedFDeriv ℝ k u (x₀ + xi • e) - iteratedFDeriv ℝ k u x₀‖
        ≤ C * ‖e‖ ^ β := by
      have h := hhold (x₀ + xi • e) (hmem xi hximem) x₀ (Metric.mem_ball_self hρ)
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hxi.1] at h
      refine h.trans ?_
      rw [Real.mul_rpow hxi.1.le (norm_nonneg e)]
      have hstep : xi ^ β * ‖e‖ ^ β ≤ 1 * ‖e‖ ^ β :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_one hxi.1.le hxi.2.le hβ.le)
          (Real.rpow_nonneg (norm_nonneg e) β)
      calc C * (xi ^ β * ‖e‖ ^ β) ≤ C * (1 * ‖e‖ ^ β) := mul_le_mul_of_nonneg_left hstep hC
        _ = C * ‖e‖ ^ β := by rw [one_mul]
    -- Step 5: reconcile the natural power from the operator bound with the real exponent.
    have hrpow : ‖e‖ ^ β * ‖e‖ ^ k = ‖e‖ ^ ((k : ℝ) + β) := by
      rw [Real.rpow_add hepos, Real.rpow_natCast]
      ring
    have hnum : |(iteratedFDeriv ℝ k u (x₀ + xi • e) - iteratedFDeriv ℝ k u x₀)
        (fun _ : Fin k => e)| ≤ C * ‖e‖ ^ ((k : ℝ) + β) := by
      rw [← hrpow, ← Real.norm_eq_abs]
      calc ‖(iteratedFDeriv ℝ k u (x₀ + xi • e) - iteratedFDeriv ℝ k u x₀)
            (fun _ : Fin k => e)‖
          ≤ ‖iteratedFDeriv ℝ k u (x₀ + xi • e) - iteratedFDeriv ℝ k u x₀‖ * ‖e‖ ^ k := hopn
        _ ≤ C * ‖e‖ ^ β * ‖e‖ ^ k :=
            mul_le_mul_of_nonneg_right hholder (by positivity)
        _ = C * (‖e‖ ^ β * ‖e‖ ^ k) := by ring
    calc |u x|
        = |(iteratedFDeriv ℝ k u (x₀ + xi • e) - iteratedFDeriv ℝ k u x₀)
            (fun _ : Fin k => e)| / (Nat.factorial k : ℝ) := by
          rw [hux, hTay, hdiag, abs_div, abs_of_pos hfacpos]
      _ ≤ C * ‖e‖ ^ ((k : ℝ) + β) / (Nat.factorial k : ℝ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = C / (Nat.factorial k : ℝ) * ‖e‖ ^ ((k : ℝ) + β) := by ring
