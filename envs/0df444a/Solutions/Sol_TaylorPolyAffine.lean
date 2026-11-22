-- Prove2me | solution 1 for TaylorPolyAffine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:15:04.981168+00:00
-- url     : https://prove2.me/submissions/775522e2-55b4-449b-bfb9-eb1791e0ea5c

import Definitions.Def_PHigherOrder_TaylorPolyRescale
import Definitions.Def_PHigherOrder_TaylorPolyAffine
import Theorems.Thm_TaylorPolyRescale


set_option autoImplicit false

theorem _root_.solution (k : ℕ) (u : Plane → ℝ) (x₀ : Plane) (ρ : ℝ) (hρ : 0 < ρ)
    (hu : ContDiffOn ℝ (k : ℕ∞) u (Metric.ball x₀ ρ))
    (r : ℝ) (hr : 0 < r) (M : ℝ) (hM : 0 < M)
    (w : Plane → ℝ) (hw : ∀ y : Plane, w y = (u (x₀ + r • y) - u x₀) / M) :
    (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ e : Plane,
        iteratedFDeriv ℝ j w 0 (fun _ => e)
          = (r ^ j / M) * iteratedFDeriv ℝ j u x₀ (fun _ => e))
      ∧ (∀ z : Plane, TaylorPoly k u x₀ z = u x₀ + M * TaylorPoly k w 0 (r⁻¹ • (z - x₀))) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hMne : M ≠ 0 := ne_of_gt hM
  -- Step 1: the translated function
  set u₁ : Plane → ℝ := fun y => u (x₀ + y) with hu₁def
  have htrans : ∀ (j : ℕ) (y : Plane), iteratedFDeriv ℝ j u₁ y = iteratedFDeriv ℝ j u (x₀ + y) :=
    fun j y => iteratedFDeriv_comp_add_left j x₀ y
  have hball0 : ∀ y ∈ Metric.ball (0 : Plane) ρ, x₀ + y ∈ Metric.ball x₀ ρ := by
    intro y hy
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  have hu₁ : ContDiffOn ℝ (k : ℕ∞) u₁ (Metric.ball (0 : Plane) ρ) :=
    hu.comp ((contDiff_const.add contDiff_id).contDiffOn) (fun y hy => hball0 y hy)
  -- Step 2: the dilation, by the within-a-set composition rule on open sets
  set L : Plane →L[ℝ] Plane := r • ContinuousLinearMap.id ℝ Plane with hL
  have hLapp : ∀ y : Plane, L y = r • y := fun y => rfl
  have hsopen : IsOpen (Metric.ball (0 : Plane) ρ) := Metric.isOpen_ball
  have hpreopen : IsOpen (L ⁻¹' Metric.ball (0 : Plane) ρ) := hsopen.preimage L.continuous
  have h0s : (0 : Plane) ∈ Metric.ball (0 : Plane) ρ := Metric.mem_ball_self hρ
  have hL0 : L 0 = (0 : Plane) := by rw [hLapp]; simp
  have h0pre : (0 : Plane) ∈ L ⁻¹' Metric.ball (0 : Plane) ρ := by
    simpa [Set.mem_preimage, hL0] using h0s
  set g : Plane → ℝ := fun y => u₁ (L y) with hgdef
  have hgCD : ContDiffOn ℝ (k : ℕ∞) g (L ⁻¹' Metric.ball (0 : Plane) ρ) :=
    hu₁.comp L.contDiff.contDiffOn (Set.Subset.refl _)
  have hgAt : ∀ j : ℕ, j ≤ k → ContDiffAt ℝ j g 0 := fun j hj =>
    (hgCD.contDiffAt (hpreopen.mem_nhds h0pre)).of_le (by exact_mod_cast hj)
  have hstep : ∀ j : ℕ, j ≤ k → iteratedFDeriv ℝ j g 0
      = (iteratedFDeriv ℝ j u₁ 0).compContinuousLinearMap (fun _ => L) := by
    intro j hj
    have h := L.iteratedFDerivWithin_comp_right hu₁ hsopen.uniqueDiffOn hpreopen.uniqueDiffOn
      (x := (0 : Plane)) (by simpa [hL0] using h0s) (i := j) (by exact_mod_cast hj)
    rw [iteratedFDerivWithin_of_isOpen (f := u₁ ∘ L) j hpreopen h0pre] at h
    rw [hgdef]
    rw [show (fun y : Plane => u₁ (L y)) = u₁ ∘ L from rfl, h, hL0,
      iteratedFDerivWithin_of_isOpen (f := u₁) j hsopen h0s]
  have hdil : ∀ j : ℕ, j ≤ k → ∀ e : Plane,
      iteratedFDeriv ℝ j g 0 (fun _ => e) = r ^ j * iteratedFDeriv ℝ j u x₀ (fun _ => e) := by
    intro j hj e
    rw [hstep j hj, ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have hrw : (fun _ : Fin j => L e) = fun _ : Fin j => r • e := by funext i; rw [hLapp]
    rw [hrw, (iteratedFDeriv ℝ j u₁ 0).map_smul_univ (fun _ => r) (fun _ => e), htrans j 0]
    simp
  -- Step 3: strip the additive constant and the scalar
  set hfun : Plane → ℝ := fun y => g y - u x₀ with hfundef
  have hfunAt : ∀ j : ℕ, j ≤ k → ContDiffAt ℝ j hfun 0 := fun j hj =>
    (hgAt j hj).sub contDiffAt_const
  have hweq : w = fun y => (M⁻¹ : ℝ) • hfun y := by
    funext y
    rw [hw y, hfundef]
    simp [hgdef, hu₁def, hLapp, div_eq_inv_mul]
  have hjet : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ e : Plane,
      iteratedFDeriv ℝ j w 0 (fun _ => e)
        = (r ^ j / M) * iteratedFDeriv ℝ j u x₀ (fun _ => e) := by
    intro j hj1 hjk e
    have hjne : j ≠ 0 := by omega
    have hconst : iteratedFDeriv ℝ j (fun _ : Plane => u x₀) 0 = 0 :=
      congrFun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := Plane) (n := j) hjne (u x₀)) 0
    have hsub : iteratedFDeriv ℝ j hfun 0 = iteratedFDeriv ℝ j g 0 := by
      rw [hfundef]
      rw [show (fun y : Plane => g y - u x₀) = g - (fun _ : Plane => u x₀) from rfl,
        iteratedFDeriv_sub_apply (hgAt j hjk) contDiffAt_const, hconst, sub_zero]
    rw [hweq, iteratedFDeriv_const_smul_apply' (hfunAt j hjk), hsub,
      smul_apply, smul_eq_mul, hdil j hjk e]
    field_simp
  have hw0 : w 0 = 0 := by rw [hw 0]; simp
  refine ⟨hjet, ?_⟩
  intro z
  unfold TaylorPoly
  rw [Finset.mul_sum, Finset.sum_range_succ' (n := k), Finset.sum_range_succ' (n := k)]
  have hzero : (1 / (Nat.factorial 0 : ℝ)) * iteratedFDeriv ℝ 0 u x₀ (fun _ => z - x₀)
      = u x₀ := by simp
  have hzero' : M * ((1 / (Nat.factorial 0 : ℝ))
      * iteratedFDeriv ℝ 0 w 0 (fun _ => r⁻¹ • (z - x₀) - 0)) = 0 := by
    simp [hw0]
  rw [hzero, hzero', add_zero]
  have hterms : ∀ i ∈ Finset.range k,
      M * ((1 / (Nat.factorial (i + 1) : ℝ))
          * iteratedFDeriv ℝ (i + 1) w 0 (fun _ => r⁻¹ • (z - x₀) - 0))
        = (1 / (Nat.factorial (i + 1) : ℝ))
          * iteratedFDeriv ℝ (i + 1) u x₀ (fun _ => z - x₀) := by
    intro i hi
    have hik : i + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.1 hi)
    rw [sub_zero, hjet (i + 1) (Nat.succ_le_succ (Nat.zero_le i)) hik]
    rw [(iteratedFDeriv ℝ (i + 1) u x₀).map_smul_univ (fun _ => r⁻¹) (fun _ => z - x₀)]
    have hprod : (∏ _j : Fin (i + 1), r⁻¹) = (r⁻¹) ^ (i + 1) := by simp
    rw [hprod]
    have hpi : r ^ i * r⁻¹ ^ i = 1 := by rw [← mul_pow, mul_inv_cancel₀ hrne, one_pow]
    field_simp
    ring_nf
    calc (r * r ^ i * (iteratedFDeriv ℝ (i + 1) u x₀ fun _ => z - x₀)) * r⁻¹ * r⁻¹ ^ i
        = (r * r⁻¹) * (r ^ i * r⁻¹ ^ i)
            * (iteratedFDeriv ℝ (i + 1) u x₀ fun _ => z - x₀) := by ring
      _ = iteratedFDeriv ℝ (i + 1) u x₀ (fun _ => z - x₀) := by
            rw [mul_inv_cancel₀ hrne, hpi, one_mul, one_mul]
  rw [Finset.sum_congr rfl hterms, add_comm]
