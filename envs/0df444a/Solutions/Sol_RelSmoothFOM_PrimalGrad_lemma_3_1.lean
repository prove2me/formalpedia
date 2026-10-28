-- Prove2me | solution 1 for RelSmoothFOM.PrimalGrad.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:39:59.291719+00:00
-- url     : https://prove2.me/submissions/b4bb1421-533b-4c67-a3b2-eb630d787806

import Definitions.Def_RelSmoothFOM_PrimalGrad_Setting
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Filter Topology RelSmoothFOM.PrimalGrad

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (Q : Set E) (hQ : Convex ℝ Q) (φ : E → ℝ) (hφ : ConvexOn ℝ Q φ) (h : E → ℝ)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (z zp : E) (hz : z ∈ Q) (hzp : zp ∈ Q)
    (hmin : ∀ u ∈ Q, φ zp + bregman h zp z ≤ φ u + bregman h u z) :
    ∀ u ∈ Q, φ u + bregman h u z ≥ φ zp + bregman h zp z + bregman h u zp := by
  intro u hu
  let d := u - zp
  let a : ℝ → E := fun t => zp + t • d
  have had : HasDerivAt a d 0 := by
    simpa only [a, id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add zp
  have hhder : HasDerivAt (fun t => h (a t)) (fderiv ℝ h zp d) 0 := by
    have hdz : HasFDerivAt h (fderiv ℝ h zp) (a 0) := by
      simpa only [a, zero_smul, add_zero] using (hhd zp hzp).hasFDerivAt
    exact hdz.comp_hasDerivAt 0 had
  have hlim : Tendsto (fun t : ℝ => (h (a t) - h zp) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (fderiv ℝ h zp d)) := by
    simpa [a, smul_eq_mul, div_eq_mul_inv, mul_comm] using hhder.tendsto_slope_zero_right
  have hlimG : Tendsto
      (fun t : ℝ => φ u - φ zp + (h (a t) - h zp) / t - fderiv ℝ h z d)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (φ u - φ zp + fderiv ℝ h zp d - fderiv ℝ h z d)) :=
    (tendsto_const_nhds.add hlim).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => fderiv ℝ h z d)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (fderiv ℝ h z d)))
  have hpos : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 ≤ φ u - φ zp + (h (a t) - h zp) / t - fderiv ℝ h z d := by
    have hsmall : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < 1 :=
      (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht0 ht1
    have htpos : 0 < t := ht0
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨htpos.le, ht1.le⟩
    have hamem : a t ∈ Q := hQ.add_smul_sub_mem hzp hu ht
    have haeq : (1 - t) • zp + t • u = a t := by
      dsimp [a, d]
      rw [sub_smul, one_smul, smul_sub]
      abel
    have hc := hφ.2 hzp hu (sub_nonneg.mpr ht1.le) htpos.le (sub_add_cancel 1 t)
    rw [haeq] at hc
    simp only [smul_eq_mul] at hc
    have hm := hmin (a t) hamem
    have hl : fderiv ℝ h z (a t - z) = fderiv ℝ h z (zp - z) + t * fderiv ℝ h z d := by
      have hv : a t - z = (zp - z) + t • d := by dsimp [a]; abel
      rw [hv, map_add, map_smul, smul_eq_mul]
    unfold bregman at hm
    rw [hl] at hm
    have hpre : 0 ≤ t * (φ u - φ zp - fderiv ℝ h z d) + h (a t) - h zp := by
      nlinarith only [hm, hc]
    by_contra! hb
    have hbad := mul_neg_of_pos_of_neg htpos hb
    have halg : t * (φ u - φ zp + (h (a t) - h zp) / t - fderiv ℝ h z d) =
        t * (φ u - φ zp - fderiv ℝ h z d) + h (a t) - h zp := by
      field_simp [htpos.ne'] <;> ring
    rw [halg] at hbad
    linarith only [hpre, hbad]
  have hle : 0 ≤ φ u - φ zp + fderiv ℝ h zp d - fderiv ℝ h z d :=
    ge_of_tendsto hlimG hpos
  dsimp [d] at hle
  unfold bregman
  simp only [map_sub] at hle ⊢
  linarith only [hle]

#print axioms solution
