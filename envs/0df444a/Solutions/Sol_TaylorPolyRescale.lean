-- Prove2me | solution 1 for TaylorPolyRescale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:10:32.068938+00:00
-- url     : https://prove2.me/submissions/4b7e3aa3-641b-4020-96a9-6ba03424d233

import Definitions.Def_PHigherOrder_TaylorPoly
import Definitions.Def_PHigherOrder_TaylorPolyRescale

set_option autoImplicit false

theorem _root_.solution (k : ℕ) (σ : ℝ) (v : Plane → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hv : ContDiffOn ℝ (k : ℕ∞) v (Metric.ball 0 ρ))
    (R : ℝ) (hR0 : 0 < R)
    (vL : Plane → ℝ) (hvL : ∀ x : Plane, vL x = v (R • x) / R ^ σ) :
    (∀ j : ℕ, j ≤ k → ∀ w : Plane,
        iteratedFDeriv ℝ j v 0 (fun _ => w)
          = R ^ (σ - (j : ℝ)) * iteratedFDeriv ℝ j vL 0 (fun _ => w))
      ∧ (∀ z : Plane, TaylorPoly k v 0 z = R ^ σ * TaylorPoly k vL 0 (R⁻¹ • z)) := by
  have hRne : R ≠ 0 := ne_of_gt hR0
  have hRs : R ^ σ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hR0 σ)
  -- the dilation, as a continuous linear map
  set L : Plane →L[ℝ] Plane := R • ContinuousLinearMap.id ℝ Plane with hL
  have hLapp : ∀ x : Plane, L x = R • x := fun x => rfl
  have hsopen : IsOpen (Metric.ball (0 : Plane) ρ) := Metric.isOpen_ball
  have hpreopen : IsOpen (L ⁻¹' Metric.ball (0 : Plane) ρ) := hsopen.preimage L.continuous
  have h0s : (0 : Plane) ∈ Metric.ball (0 : Plane) ρ := Metric.mem_ball_self hρ
  have hL0 : L 0 = (0 : Plane) := by rw [hLapp]; simp
  have h0pre : (0 : Plane) ∈ L ⁻¹' Metric.ball (0 : Plane) ρ := by
    simpa [Set.mem_preimage, hL0] using h0s
  have hcompCD : ContDiffOn ℝ (k : ℕ∞) (v ∘ L) (L ⁻¹' Metric.ball (0 : Plane) ρ) :=
    hv.comp L.contDiff.contDiffOn (Set.Subset.refl _)
  have hcompAt : ∀ j : ℕ, j ≤ k → ContDiffAt ℝ j (v ∘ L) 0 := fun j hj =>
    (hcompCD.contDiffAt (hpreopen.mem_nhds h0pre)).of_le (by exact_mod_cast hj)
  -- the derivative of `v ∘ L` at the origin, as a multilinear form
  have hstep : ∀ j : ℕ, j ≤ k → iteratedFDeriv ℝ j (v ∘ L) 0
      = (iteratedFDeriv ℝ j v 0).compContinuousLinearMap (fun _ => L) := by
    intro j hj
    have h := L.iteratedFDerivWithin_comp_right hv hsopen.uniqueDiffOn hpreopen.uniqueDiffOn
      (x := (0 : Plane)) (by simpa [hL0] using h0s) (i := j) (by exact_mod_cast hj)
    rw [iteratedFDerivWithin_of_isOpen (f := v ∘ L) j hpreopen h0pre] at h
    rw [h, hL0, iteratedFDerivWithin_of_isOpen (f := v) j hsopen h0s]
  -- on the diagonal the linear map contributes `R ^ j`
  have hdiag : ∀ (j : ℕ) (w : Plane),
      (iteratedFDeriv ℝ j v 0).compContinuousLinearMap (fun _ => L) (fun _ => w)
        = R ^ (j : ℕ) * iteratedFDeriv ℝ j v 0 (fun _ => w) := by
    intro j w
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have hrw : (fun _ : Fin j => L w) = fun _ : Fin j => R • w := by funext i; rw [hLapp]
    rw [hrw, (iteratedFDeriv ℝ j v 0).map_smul_univ (fun _ => R) (fun _ => w)]
    simp
  -- the jet identity, in the form that is convenient for both conclusions
  have hkey : ∀ j : ℕ, j ≤ k → ∀ w : Plane,
      iteratedFDeriv ℝ j vL 0 (fun _ => w)
        = (R ^ σ)⁻¹ * (R ^ (j : ℕ) * iteratedFDeriv ℝ j v 0 (fun _ => w)) := by
    intro j hj w
    have hvLeq : vL = fun x => (R ^ σ)⁻¹ • (v ∘ L) x := by
      funext x
      rw [hvL x]
      simp [Function.comp, hLapp, div_eq_inv_mul]
    rw [hvLeq, iteratedFDeriv_const_smul_apply' (hcompAt j hj), smul_apply, smul_eq_mul,
      hstep j hj, hdiag j w]
  have hmul : ∀ j : ℕ, R ^ (σ - (j : ℝ)) * R ^ (j : ℕ) = R ^ σ := by
    intro j
    rw [← Real.rpow_natCast R j, ← Real.rpow_add hR0]
    congr 1
    ring
  refine ⟨fun j hj w => ?_, fun z => ?_⟩
  · have h1 : R ^ (σ - (j : ℝ))
          * ((R ^ σ)⁻¹ * (R ^ (j : ℕ) * iteratedFDeriv ℝ j v 0 (fun _ => w)))
        = (R ^ (σ - (j : ℝ)) * R ^ (j : ℕ))
          * ((R ^ σ)⁻¹ * iteratedFDeriv ℝ j v 0 (fun _ => w)) := by
      ring
    rw [hkey j hj w, h1, hmul j, mul_inv_cancel_left₀ hRs]
  · simp only [TaylorPoly, sub_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := by have := Finset.mem_range.1 hj; omega
    have hhom : iteratedFDeriv ℝ j vL 0 (fun _ => R⁻¹ • z)
        = (R⁻¹) ^ (j : ℕ) * iteratedFDeriv ℝ j vL 0 (fun _ => z) := by
      rw [(iteratedFDeriv ℝ j vL 0).map_smul_univ (fun _ => R⁻¹) (fun _ => z)]
      simp
    rw [hhom, hkey j hjk z]
    field_simp
    rw [mul_assoc, ← mul_pow, one_div, inv_mul_cancel₀ hRne, one_pow, mul_one]
