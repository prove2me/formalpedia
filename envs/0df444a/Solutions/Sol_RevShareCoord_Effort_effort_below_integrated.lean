-- Prove2me | solution 1 for RevShareCoord.Effort.effort_below_integrated
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:16:01.718907+00:00
-- url     : https://prove2.me/submissions/e8db76e4-ae99-49fe-9904-4cc36107f82f

import Mathlib
import Definitions.Def_RevShareCoord_Effort_Model

open RevShareCoord.Effort in
theorem solution (M : Model) (qI eI : ℝ) (hqI : 0 < qI) (heI : 0 < eI)
    (hopt : IsMaxOn (fun x : ℝ × ℝ => M.Pi x.1 x.2) (Set.Ici 0 ×ˢ Set.Ici 0) (qI, eI))
    (hRe : 0 < M.Re qI eI)
    (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) (fun e => φ * M.R qI e - M.g e)) :
    ∀ e : ℝ, 0 ≤ e →
      IsMaxOn (fun e' => M.retailerProfit φ (φ * M.c) qI e') (Set.Ici 0) e → e < eI := by
  intro e he hmax
  set G : ℝ → ℝ := fun e => φ * M.R qI e - M.g e with hG
  have hGmax : ∀ y, 0 ≤ y → G y ≤ G e := by
    intro y hy
    have := hmax (Set.mem_Ici.mpr hy)
    simp only [Set.mem_setOf_eq, Model.retailerProfit] at this
    simp only [hG]
    linarith
  have hnhds : Set.Ici (0:ℝ) ∈ nhds eI := Ici_mem_nhds heI
  have h1 := (M.hasDeriv_e qI eI hqI.le heI.le).hasDerivAt hnhds
  have h2 := (M.hasDeriv_g eI heI.le).hasDerivAt hnhds
  have hPi : HasDerivAt (fun e => M.Pi qI e) (M.Re qI eI - M.g' eI) eI := by
    have := (h1.sub h2).sub_const (qI * M.c)
    exact this
  have hloc : IsLocalMax (fun e => M.Pi qI e) eI := by
    filter_upwards [hnhds] with y hy
    exact hopt (Set.mk_mem_prod (Set.mem_Ici.mpr hqI.le) hy)
  have hfoc := hloc.hasDerivAt_eq_zero hPi
  have hGd : HasDerivAt G (φ * M.Re qI eI - M.g' eI) eI := (h1.const_mul φ).sub h2
  have hneg : φ * M.Re qI eI - M.g' eI < 0 := by nlinarith
  by_contra hle
  push_neg at hle
  rcases hle.lt_or_eq with hlt | heq
  · have hcv : ConvexOn ℝ (Set.Ici 0) (fun y => -G y) := hconc.concaveOn.neg
    have hs := hcv.le_slope_of_hasDerivAt (Set.mem_Ici.mpr heI.le) (Set.mem_Ici.mpr he) hlt
      hGd.neg
    rw [slope_def_field] at hs
    have h3 := hGmax eI heI.le
    have hpos : 0 < e - eI := by linarith
    rw [le_div_iff₀ hpos] at hs
    nlinarith
  · have hloc2 : IsLocalMax G eI := by
      filter_upwards [hnhds] with y hy
      rw [heq]
      exact hGmax y hy
    have := hloc2.hasDerivAt_eq_zero hGd
    linarith
