-- Prove2me | solution 1 for ProjSelfConcordant.ConicExt.hessian_third_expansion
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:16:24.40551+00:00
-- url     : https://prove2.me/submissions/e3263a4a-dbe1-4c1f-a7dc-d150c3983ee9

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting

open ProjSelfConcordant.ConicExt Filter
open scoped Topology

namespace ProjSelfConcordant.ConicExt.Expansion

theorem line_derivs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (x h : E) (hg : ContDiffAt ℝ 3 g x) :
    deriv (fun t : ℝ => g (x + t • h)) 0 = dk 1 g x h ∧
    iteratedDeriv 2 (fun t : ℝ => g (x + t • h)) 0 = dk 2 g x h ∧
    iteratedDeriv 3 (fun t : ℝ => g (x + t • h)) 0 = dk 3 g x h := by
  let c := fun t : ℝ => x + t • h
  have hc : ContDiffAt ℝ 3 c 0 := by dsimp [c]; fun_prop
  have hc0 : c 0 = x := by simp [c]
  have hc1 : HasDerivAt c h 0 := by
    simpa [c] using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add x
  have hc2 : iteratedDeriv 2 c 0 = 0 := by
    rw [iteratedDeriv_const_add (by norm_num), iteratedDeriv_smul_const contDiffAt_id]
    simp [iteratedDeriv_fun_id]
  have hc3 : iteratedDeriv 3 c 0 = 0 := by
    rw [iteratedDeriv_const_add (by norm_num), iteratedDeriv_smul_const contDiffAt_id]
    simp [iteratedDeriv_fun_id]
  have hg' : ContDiffAt ℝ 3 g (c 0) := hc0.symm ▸ hg
  have hz1 : iteratedFDeriv ℝ 2 g x ![0, h] = 0 :=
    (iteratedFDeriv ℝ 2 g x).map_coord_zero 0 rfl
  have hz2 : iteratedFDeriv ℝ 2 g x ![h, 0] = 0 :=
    (iteratedFDeriv ℝ 2 g x).map_coord_zero 1 rfl
  refine ⟨?_, ?_, ?_⟩
  · simpa [dk, iteratedFDeriv_one_apply, c, Function.comp_def] using
      ((hg'.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 hc1).deriv
  · simpa [Function.comp_def, hc0, hc1.deriv, hc2, dk, c] using
      iteratedDeriv_vcomp_two (hg'.of_le (by norm_num)) (hc.of_le (by norm_num))
  · simpa only [hc0, hc1.deriv, hc2, hc3, hz1, hz2, map_zero, smul_zero,
      add_zero, dk, Function.comp_def] using iteratedDeriv_vcomp_three hg' hc

theorem inv_line (α : ℝ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => (α * t + 1)⁻¹) 0 =
      (-1 : ℝ) ^ k * k.factorial * α ^ k := by
  rw [iteratedDeriv_eq_iterate, iter_deriv_inv_linear]
  simp

theorem rational_derivs (α : ℝ) :
    deriv (fun t : ℝ => t * (α * t + 1)⁻¹) 0 = 1 ∧
    iteratedDeriv 2 (fun t : ℝ => t * (α * t + 1)⁻¹) 0 = -2 * α ∧
    iteratedDeriv 3 (fun t : ℝ => t * (α * t + 1)⁻¹) 0 = 6 * α ^ 2 := by
  have hi (k : ℕ) : ContDiffAt ℝ k (fun t : ℝ => (α * t + 1)⁻¹) 0 := by
    apply ContDiffAt.inv
    · fun_prop
    · norm_num
  have hprod (k : ℕ) := iteratedDeriv_fun_mul (n := k) (x := (0 : ℝ))
      (f := fun t : ℝ => t) (g := fun t : ℝ => (α * t + 1)⁻¹) contDiffAt_id (hi k)
  refine ⟨?_, ?_, ?_⟩
  · simpa [Finset.sum_range_succ, iteratedDeriv_fun_id, inv_line] using hprod 1
  · simpa [Finset.sum_range_succ, iteratedDeriv_fun_id, inv_line] using hprod 2
  · have hp := hprod 3
    norm_num [Finset.sum_range_succ, iteratedDeriv_fun_id, inv_line] at hp
    linarith

theorem log_line_derivs (α : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => Real.log (α * t + 1)) 0 = -α ^ 2 ∧
    iteratedDeriv 3 (fun t : ℝ => Real.log (α * t + 1)) 0 = 2 * α ^ 3 := by
  have he : ∀ᶠ t : ℝ in 𝓝 0, α * t + 1 ≠ 0 := by
    exact (show ContinuousAt (fun t : ℝ => α * t + 1) 0 by fun_prop).eventually_ne (by norm_num)
  have hd : deriv (fun t : ℝ => Real.log (α * t + 1)) =ᶠ[𝓝 0]
      (fun t : ℝ => α * (α * t + 1)⁻¹) := by
    filter_upwards [he] with t ht
    simpa [div_eq_mul_inv] using (((hasDerivAt_id t).const_mul α).add_const 1).log ht |>.deriv
  constructor
  · rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ', hd.iteratedDeriv_eq 1,
        iteratedDeriv_const_mul_field, inv_line]
    norm_num
    ring
  · rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ', hd.iteratedDeriv_eq 2,
        iteratedDeriv_const_mul_field, inv_line]
    norm_num
    ring

end ProjSelfConcordant.ConicExt.Expansion

open ProjSelfConcordant.ConicExt.Expansion

theorem solution {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (hDo : IsOpen D) (hDc : Convex ℝ D)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiffOn ℝ 3 f D) (ν : ℝ)
    (xt : EuclideanSpace ℝ (Fin n)) (hxt : xt ∈ D) (vt : EuclideanSpace ℝ (Fin n)) (α : ℝ) :
    dk 2 (homExt ν f) ((1 : ℝ), xt) (α, vt + α • xt)
        = ν * (α ^ 2 - 2 * α * dk 1 f xt vt + dk 2 f xt vt) ∧
      dk 3 (homExt ν f) ((1 : ℝ), xt) (α, vt + α • xt)
        = ν * (-2 * α ^ 3 + 6 * α ^ 2 * dk 1 f xt vt - 6 * α * dk 2 f xt vt + dk 3 f xt vt) := by
  clear hDc
  have hfAt : ContDiffAt ℝ 3 f xt := hf.contDiffAt (hDo.mem_nhds hxt)
  let g := fun t : ℝ => f (xt + t • vt)
  let r := fun t : ℝ => t * (α * t + 1)⁻¹
  have hr0 : r 0 = 0 := by simp [r]
  have hg : ContDiffAt ℝ 3 g 0 := by
    apply ContDiffAt.comp (f := fun t : ℝ => xt + t • vt)
    · simpa using hfAt
    · fun_prop
  have hr : ContDiffAt ℝ 3 r 0 := by
    apply contDiffAt_id.mul
    apply ContDiffAt.inv
    · fun_prop
    · norm_num
  have hgcomp : ContDiffAt ℝ 3 (g ∘ r) 0 := (hr0.symm ▸ hg).comp 0 hr
  change ContDiffAt ℝ 3 (fun t => g (r t)) 0 at hgcomp
  have hl : ContDiffAt ℝ 3 (fun t : ℝ => Real.log (α * t + 1)) 0 := by
    apply ContDiffAt.log
    · fun_prop
    · norm_num
  have hF : ContDiffAt ℝ 3 (homExt ν f) ((1 : ℝ), xt) := by
    apply contDiffAt_const.mul
    apply ContDiffAt.add
    · apply ContDiffAt.neg
      exact contDiffAt_fst.log (by norm_num)
    · apply ContDiffAt.comp (f := fun q : ℝ × EuclideanSpace ℝ (Fin n) => q.1⁻¹ • q.2)
      · simpa using hfAt
      · exact (contDiffAt_fst.inv (by norm_num)).smul contDiffAt_snd
  have he : ∀ᶠ t : ℝ in 𝓝 0, α * t + 1 ≠ 0 :=
    (show ContinuousAt (fun t : ℝ => α * t + 1) 0 by fun_prop).eventually_ne (by norm_num)
  have heq : (fun t : ℝ => homExt ν f (((1 : ℝ), xt) + t • (α, vt + α • xt)))
      =ᶠ[𝓝 0] (fun t : ℝ => ν * (-Real.log (α * t + 1) + g (r t))) := by
    filter_upwards [he] with t ht
    have ht' : (1 : ℝ) + t * α = α * t + 1 := by ring
    have hx : (α * t + 1)⁻¹ • (xt + t • (vt + α • xt)) =
        xt + (t * (α * t + 1)⁻¹) • vt := by
      have hs : (α * t + 1)⁻¹ + (α * t + 1)⁻¹ * t * α = 1 := by
        field_simp
        ring
      calc
        _ = ((α * t + 1)⁻¹ + (α * t + 1)⁻¹ * t * α) • xt +
            (t * (α * t + 1)⁻¹) • vt := by module
        _ = _ := by rw [hs, one_smul]
    simp only [homExt, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
      smul_eq_mul, ht', hx, g, r]
  obtain ⟨hg1, hg2, hg3⟩ := line_derivs f xt vt hfAt
  obtain ⟨hF1, hF2, hF3⟩ := line_derivs (homExt ν f) ((1 : ℝ), xt) (α, vt + α • xt) hF
  obtain ⟨hr1, hr2, hr3⟩ := rational_derivs α
  obtain ⟨hl2, hl3⟩ := log_line_derivs α
  have hc2 := iteratedDeriv_comp_two ((hr0.symm ▸ hg).of_le (by norm_num)) (hr.of_le (by norm_num))
  have hc3 := iteratedDeriv_comp_three (hr0.symm ▸ hg) hr
  have heq2 := heq.iteratedDeriv_eq 2
  have heq3 := heq.iteratedDeriv_eq 3
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_add
    (hl.neg.of_le (by norm_num)) (hgcomp.of_le (by norm_num)), iteratedDeriv_fun_neg,
    hl2, hF2] at heq2
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_add hl.neg hgcomp,
    iteratedDeriv_fun_neg, hl3, hF3] at heq3
  dsimp [g, r, Function.comp_def] at hc2 hc3
  rw [show (0 : ℝ) * (α * 0 + 1)⁻¹ = 0 by simp, hr1, hr2, hg1, hg2] at hc2
  rw [show (0 : ℝ) * (α * 0 + 1)⁻¹ = 0 by simp, hr1, hr2, hr3, hg1, hg2, hg3] at hc3
  constructor
  · rw [heq2]
    dsimp [g, r]
    rw [hc2]
    ring
  · rw [heq3]
    dsimp [g, r]
    rw [hc3]
    ring
