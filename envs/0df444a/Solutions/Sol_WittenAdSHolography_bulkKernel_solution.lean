-- Prove2me | solution 1 for WittenAdSHolography.bulkKernel_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T00:12:29.594765+00:00
-- url     : https://prove2.me/submissions/9682647c-9164-4c3f-8696-1df375cbbdec

import Mathlib
import Definitions.Def_WittenAdSHolography_Defs

set_option autoImplicit false

namespace BK5c96
open WittenAdSHolography

lemma kd {Δ : ℝ} {a b : ℝ → ℝ} {a' b' s : ℝ} (ha : HasDerivAt a a' s) (hb : HasDerivAt b b' s)
    (ha0 : 0 < a s) (hb0 : 0 < b s) :
    HasDerivAt (fun s => a s ^ Δ / b s ^ Δ)
      (Δ * (a s ^ Δ / b s ^ Δ) * (a' / a s - b' / b s)) s := by
  have h := (ha.rpow_const (p := Δ) (Or.inl ha0.ne')).div
    (hb.rpow_const (p := Δ) (Or.inl hb0.ne')) (Real.rpow_pos_of_pos hb0 Δ).ne'
  refine h.congr_deriv ?_
  rw [Real.rpow_sub_one ha0.ne', Real.rpow_sub_one hb0.ne']
  have h1 : 0 < a s ^ Δ := Real.rpow_pos_of_pos ha0 Δ
  have h2 : 0 < b s ^ Δ := Real.rpow_pos_of_pos hb0 Δ
  field_simp

lemma hd0 {d : ℕ} (Δ : ℝ) (y : Bdry d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => bulkKernel (d := d) Δ t y)
      (Δ * bulkKernel Δ t y * (1 / t - 2 * t / (t ^ 2 + ‖y‖ ^ 2))) t := by
  have hb : HasDerivAt (fun t : ℝ => t ^ 2 + ‖y‖ ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const (‖y‖ ^ 2)
  exact kd (a := fun t => t) (hasDerivAt_id' t) hb ht (by positivity)

lemma hcurve {d : ℕ} (x₀ : ℝ) (y e : Bdry d) (s : ℝ) :
    HasDerivAt (fun s : ℝ => x₀ ^ 2 + ‖y + s • e‖ ^ 2) (2 * inner ℝ (y + s • e) e) s := by
  have h1 : HasDerivAt (fun s : ℝ => y + s • e) e s := by
    simpa using ((hasDerivAt_id' s).smul_const e).const_add y
  exact (h1.norm_sq).const_add _

lemma hdjK {d : ℕ} (Δ : ℝ) {x₀ : ℝ} (hx₀ : 0 < x₀) (y e : Bdry d) (s : ℝ) :
    HasDerivAt (fun s : ℝ => bulkKernel (d := d) Δ x₀ (y + s • e))
      (Δ * bulkKernel Δ x₀ (y + s • e) *
        (0 / x₀ - 2 * inner ℝ (y + s • e) e / (x₀ ^ 2 + ‖y + s • e‖ ^ 2))) s := by
  have hp : 0 < x₀ ^ 2 + ‖y + s • e‖ ^ 2 := by positivity
  exact kd (a := fun _ => x₀) (hasDerivAt_const s x₀) (hcurve x₀ y e s) hx₀ hp

lemma dj_eq {d : ℕ} (Δ : ℝ) {x₀ : ℝ} (hx₀ : 0 < x₀) (j : Fin d) (y : Bdry d) :
    dj j (fun x₀ x => bulkKernel Δ x₀ x) x₀ y
      = -(2 * Δ) * bulkKernel Δ x₀ y * y j / (x₀ ^ 2 + ‖y‖ ^ 2) := by
  simp only [dj]
  rw [(hdjK Δ hx₀ y (EuclideanSpace.single j (1 : ℝ)) 0).deriv]
  simp [EuclideanSpace.inner_single_right]
  ring

lemma djj_eq {d : ℕ} (Δ : ℝ) {x₀ : ℝ} (hx₀ : 0 < x₀) (j : Fin d) (x : Bdry d) :
    dj j (dj j (fun x₀ x => bulkKernel Δ x₀ x)) x₀ x
      = -(2 * Δ) * bulkKernel Δ x₀ x * (1 / (x₀ ^ 2 + ‖x‖ ^ 2)
          - 2 * (Δ + 1) * (x j) ^ 2 / (x₀ ^ 2 + ‖x‖ ^ 2) ^ 2) := by
  set e : Bdry d := EuclideanSpace.single j (1 : ℝ) with he
  have hlin : ∀ s : ℝ, (x + s • e) j = x j + s := by intro s; simp [he]
  have hin : ∀ s : ℝ, inner ℝ (x + s • e) e = x j + s := by
    intro s; rw [he, EuclideanSpace.inner_single_right]; simp [he]
  show deriv (fun s : ℝ => dj j (fun x₀ x => bulkKernel Δ x₀ x) x₀ (x + s • e)) 0 = _
  simp only [dj_eq Δ hx₀ j]
  have hc : HasDerivAt (fun s : ℝ => (x + s • e) j) 1 0 := by
    simp only [hlin]
    simpa using (hasDerivAt_id' (0:ℝ)).const_add (x j)
  have hb := hcurve x₀ x e 0
  have hK := hdjK Δ hx₀ x e 0
  have hbpos : 0 < x₀ ^ 2 + ‖x + (0:ℝ) • e‖ ^ 2 := by positivity
  have h : HasDerivAt (fun s : ℝ => -(2 * Δ) * bulkKernel Δ x₀ (x + s • e) * (x + s • e) j
      / (x₀ ^ 2 + ‖x + s • e‖ ^ 2)) _ 0 := ((hK.const_mul (-(2 * Δ))).mul hc).div hb hbpos.ne'
  rw [h.deriv]
  have hin0 : inner ℝ x e = x j := by simpa using hin 0
  simp only [Pi.mul_apply, zero_smul, add_zero, hin0]
  have hS : 0 < x₀ ^ 2 + ‖x‖ ^ 2 := by positivity
  field_simp
  ring

end BK5c96

open WittenAdSHolography MeasureTheory Filter Topology in
theorem solution (d : ℕ) (msq Δ : ℝ) (hΔ : Δ * (Δ - d) = msq) :
    IsMassiveSolution d msq (fun x₀ x => bulkKernel Δ x₀ x) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    have hp1 : 0 < p.1 := (Set.mem_prod.mp hp).1
    have hS : 0 < p.1 ^ 2 + ‖p.2‖ ^ 2 := by positivity
    have h1 : ContDiffAt ℝ 2 (fun q : ℝ × Bdry d => q.1 ^ Δ) p :=
      ContDiffAt.rpow_const_of_ne contDiffAt_fst hp1.ne'
    have h2 : ContDiffAt ℝ 2 (fun q : ℝ × Bdry d => (q.1 ^ 2 + ‖q.2‖ ^ 2) ^ Δ) p := by
      exact ContDiffAt.rpow_const_of_ne (f := fun q : ℝ × Bdry d => q.1 ^ 2 + ‖q.2‖ ^ 2)
        ((contDiffAt_fst.pow 2).add ((contDiff_norm_sq ℝ).contDiffAt.comp p contDiffAt_snd))
        hS.ne'
    exact (h1.div h2 (Real.rpow_pos_of_pos hS Δ).ne').contDiffWithinAt
  · intro x₀ hx₀ x
    set u : ℝ → Bdry d → ℝ := fun x₀ x => bulkKernel Δ x₀ x with hu
    -- first derivative in x₀ as a function
    set D1 : ℝ → ℝ := fun t => Δ * bulkKernel (d := d) Δ t x * (1 / t - 2 * t / (t ^ 2 + ‖x‖ ^ 2))
      with hD1
    have hev : (fun t => d0 u t x) =ᶠ[𝓝 x₀] D1 := by
      filter_upwards [Ioi_mem_nhds hx₀] with t ht
      exact (BK5c96.hd0 Δ x ht).deriv
    have hdd : d0 (d0 u) x₀ x = deriv D1 x₀ := hev.deriv_eq
    have hS : 0 < x₀ ^ 2 + ‖x‖ ^ 2 := by positivity
    have hb : HasDerivAt (fun t : ℝ => t ^ 2 + ‖x‖ ^ 2) (2 * x₀) x₀ := by
      simpa using (hasDerivAt_pow 2 x₀).add_const (‖x‖ ^ 2)
    have hg : HasDerivAt (fun t : ℝ => 1 / t - 2 * t / (t ^ 2 + ‖x‖ ^ 2))
        ((0 * x₀ - 1 * 1) / x₀ ^ 2 - ((2 * 1) * (x₀ ^ 2 + ‖x‖ ^ 2) - 2 * x₀ * (2 * x₀))
          / (x₀ ^ 2 + ‖x‖ ^ 2) ^ 2) x₀ :=
      ((hasDerivAt_const x₀ (1:ℝ)).div (hasDerivAt_id' x₀) hx₀.ne').sub
        (((hasDerivAt_id' x₀).const_mul 2).div hb hS.ne')
    have hD : HasDerivAt D1 _ x₀ := ((BK5c96.hd0 (d := d) Δ x hx₀).const_mul Δ).mul hg
    have hsum : ∑ j : Fin d, dj j (dj j u) x₀ x
        = (d : ℝ) * (-(2 * Δ) * bulkKernel Δ x₀ x * (1 / (x₀ ^ 2 + ‖x‖ ^ 2)))
            + (4 * Δ * (Δ + 1) * bulkKernel Δ x₀ x / (x₀ ^ 2 + ‖x‖ ^ 2) ^ 2) * ‖x‖ ^ 2 := by
      calc ∑ j : Fin d, dj j (dj j u) x₀ x
          = ∑ j : Fin d, (-(2 * Δ) * bulkKernel Δ x₀ x * (1 / (x₀ ^ 2 + ‖x‖ ^ 2))
            + (4 * Δ * (Δ + 1) * bulkKernel Δ x₀ x / (x₀ ^ 2 + ‖x‖ ^ 2) ^ 2) * (x j) ^ 2) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [hu, BK5c96.djj_eq Δ hx₀ j x]
            ring
        _ = _ := by
            rw [EuclideanSpace.real_norm_sq_eq x, Finset.mul_sum, Finset.sum_add_distrib]
            simp
    have hd1 : d0 u x₀ x = D1 x₀ := (BK5c96.hd0 Δ x hx₀).deriv
    simp only [hypLaplacian, hdd, hsum, hd1]
    rw [hD.deriv]
    simp only [hD1, hu]
    rw [← hΔ]
    field_simp
    ring
