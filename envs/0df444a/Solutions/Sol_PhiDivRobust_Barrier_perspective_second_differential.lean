-- Prove2me | solution 1 for PhiDivRobust.Barrier.perspective_second_differential
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:54:11.27925+00:00
-- url     : https://prove2.me/submissions/695f52e8-8807-4b9a-b62e-8622a06aaf2e

import Mathlib
import Definitions.Def_PhiDivRobust_Barrier_perspective

namespace PhiDivRobust.Barrier

open Filter Topology

theorem aux_psd_hasFDeriv_div (q : ℝ × ℝ) (hq : q.2 ≠ 0) :
    HasFDerivAt (fun r : ℝ × ℝ => r.1 / r.2)
      ((1 / q.2) • ContinuousLinearMap.fst ℝ ℝ ℝ
        - (q.1 / q.2 ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ) q := by
  have h1 : HasFDerivAt (fun r : ℝ × ℝ => r.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) q :=
    hasFDerivAt_fst
  have h2 : HasFDerivAt (fun r : ℝ × ℝ => r.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
    hasFDerivAt_snd
  have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-(q.2 ^ 2)⁻¹) q.2 := hasDerivAt_inv hq
  have h3 : HasFDerivAt (fun r : ℝ × ℝ => (r.2)⁻¹)
      (-(q.2 ^ 2)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ) q := hinv.comp_hasFDerivAt q h2
  have h4 : HasFDerivAt (fun r : ℝ × ℝ => r.1 * (r.2)⁻¹)
      (q.1 • (-(q.2 ^ 2)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)
        + (q.2)⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ) q := h1.mul h3
  have e : (fun r : ℝ × ℝ => r.1 / r.2) = fun r : ℝ × ℝ => r.1 * (r.2)⁻¹ := by
    funext r; rw [div_eq_mul_inv]
  rw [e]
  refine h4.congr_fderiv ?_
  ext
  · simp
  · simp; field_simp

/-- explicit first derivative of the perspective -/
noncomputable def aux_psd_L (f : ℝ → ℝ) (q : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  deriv f (q.1 / q.2) • ContinuousLinearMap.fst ℝ ℝ ℝ
    + (f (q.1 / q.2) - q.1 / q.2 * deriv f (q.1 / q.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem aux_psd_hasFDeriv_persp (f : ℝ → ℝ) (q : ℝ × ℝ) (hq : q.2 ≠ 0)
    (hfd : DifferentiableAt ℝ f (q.1 / q.2)) :
    HasFDerivAt (perspective f) (aux_psd_L f q) q := by
  have h2 : HasFDerivAt (fun r : ℝ × ℝ => r.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
    hasFDerivAt_snd
  have hc : HasFDerivAt (fun r : ℝ × ℝ => f (r.1 / r.2))
      (deriv f (q.1 / q.2) • ((1 / q.2) • ContinuousLinearMap.fst ℝ ℝ ℝ
        - (q.1 / q.2 ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ)) q :=
    hfd.hasDerivAt.comp_hasFDerivAt q (aux_psd_hasFDeriv_div q hq)
  have h4 := h2.mul hc
  refine h4.congr_fderiv ?_
  unfold aux_psd_L
  ext
  · simp; field_simp
  · simp; field_simp; ring

theorem aux_psd_fderiv_eventually (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0))
    (p : ℝ × ℝ) (hs : 0 < p.1) (hy : 0 < p.2) :
    fderiv ℝ (perspective f) =ᶠ[𝓝 p] aux_psd_L f := by
  have hU : IsOpen {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd)
  filter_upwards [hU.mem_nhds ⟨hs, hy⟩] with q hq
  have hu : 0 < q.1 / q.2 := div_pos hq.1 hq.2
  have hdiff : DifferentiableOn ℝ f (Set.Ioi 0) := hf.differentiableOn (by norm_num)
  have hfd : DifferentiableAt ℝ f (q.1 / q.2) :=
    hdiff.differentiableAt (Ioi_mem_nhds hu)
  exact (aux_psd_hasFDeriv_persp f q hq.2.ne' hfd).fderiv

theorem aux_psd_second (f : ℝ → ℝ) (p : ℝ × ℝ) (hq : p.2 ≠ 0)
    (hfd : DifferentiableAt ℝ f (p.1 / p.2))
    (hfd2 : DifferentiableAt ℝ (deriv f) (p.1 / p.2)) (h : ℝ × ℝ) :
    fderiv ℝ (aux_psd_L f) p h h =
      deriv (deriv f) (p.1 / p.2) * (h.1 - p.1 / p.2 * h.2) ^ 2 / p.2 := by
  have hD := aux_psd_hasFDeriv_div p hq
  have ha : HasFDerivAt (fun r : ℝ × ℝ => deriv f (r.1 / r.2))
      (deriv (deriv f) (p.1 / p.2) • ((1 / p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ
        - (p.1 / p.2 ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
    have := hfd2.hasDerivAt.comp_hasFDerivAt p hD
    exact this
  have hc : HasFDerivAt (fun r : ℝ × ℝ => f (r.1 / r.2))
      (deriv f (p.1 / p.2) • ((1 / p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ
        - (p.1 / p.2 ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    hfd.hasDerivAt.comp_hasFDerivAt p hD
  have hb := hc.sub (hD.mul ha)
  have hL : HasFDerivAt (aux_psd_L f) _ p :=
    (ha.smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ)).add
      (hb.smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ))
  rw [hL.fderiv]
  simp
  field_simp
  ring

end PhiDivRobust.Barrier

open PhiDivRobust.Barrier

theorem solution (f : ℝ → ℝ) (hf : ContDiffOn ℝ 3 f (Set.Ioi 0))
    (s y : ℝ) (hs : 0 < s) (hy : 0 < y) (h : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (perspective f) (s, y) (fun _ => h) =
      iteratedDeriv 2 f (s / y) *
        (h.1 ^ 2 / y - 2 * s * h.1 * h.2 / y ^ 2 + s ^ 2 * h.2 ^ 2 / y ^ 3) := by
  have hu : 0 < s / y := div_pos hs hy
  have hdiff : DifferentiableOn ℝ f (Set.Ioi 0) := hf.differentiableOn (by norm_num)
  have hfd : DifferentiableAt ℝ f (s / y) := hdiff.differentiableAt (Ioi_mem_nhds hu)
  have hf1 : ContDiffOn ℝ 2 (deriv f) (Set.Ioi 0) :=
    hf.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdiff2 : DifferentiableOn ℝ (deriv f) (Set.Ioi 0) := hf1.differentiableOn (by norm_num)
  have hfd2 : DifferentiableAt ℝ (deriv f) (s / y) := hdiff2.differentiableAt (Ioi_mem_nhds hu)
  have hev := aux_psd_fderiv_eventually f hf (s, y) hs hy
  have hL := aux_psd_second f (s, y) hy.ne' hfd hfd2 h
  rw [iteratedFDeriv_two_apply, hev.fderiv_eq]
  rw [hL]
  have e2 : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [iteratedDeriv_succ', iteratedDeriv_one]
  rw [e2]
  field_simp
  ring
