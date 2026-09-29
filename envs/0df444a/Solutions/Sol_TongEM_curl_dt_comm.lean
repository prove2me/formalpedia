-- Prove2me | solution 1 for TongEM.curl_dt_comm
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T03:30:36.853493+00:00
-- url     : https://prove2.me/submissions/783995b8-ebea-47c7-b911-e17e48e06a2c

import Definitions.Def_TongEM_wave_ops

open TongEM Larmor

namespace DTAux

variable (F : ℝ → Vec → Vec)

/-- The joint map. -/
def G : ℝ × Vec → Vec := fun p => F p.1 p.2

lemma pd_F (hG : Differentiable ℝ (G F)) (s : ℝ) (y : Vec) (j i : Fin 3) :
    partialDeriv (F s) j i y = fderiv ℝ (G F) (s, y) (0, EuclideanSpace.single j 1) i := by
  unfold partialDeriv
  have h : HasFDerivAt (F s) ((fderiv ℝ (G F) (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ Vec)) y :=
    (hG (s, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)
  rw [h.fderiv]
  simp

lemma hasDerivAt_F (hG : Differentiable ℝ (G F)) (s : ℝ) (y : Vec) :
    HasDerivAt (fun r => F r y) (fderiv ℝ (G F) (s, y) (1, 0)) s := by
  have hp : HasDerivAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : Vec)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  exact (hG (s, y)).hasFDerivAt.comp_hasDerivAt s hp

lemma hasDerivAt_DG (hDG : Differentiable ℝ (fderiv ℝ (G F))) (t : ℝ) (x : Vec)
    (v : ℝ × Vec) (i : Fin 3) :
    HasDerivAt (fun s => fderiv ℝ (G F) (s, x) v i)
      (fderiv ℝ (fderiv ℝ (G F)) (t, x) (1, 0) v i) t := by
  have hp : HasDerivAt (fun r : ℝ => (r, x)) ((1 : ℝ), (0 : Vec)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have h1 := (hDG (t, x)).hasFDerivAt.comp_hasDerivAt t hp
  -- evaluate at `v`, then take the `i`-th coordinate
  have h2 : HasDerivAt (fun s => fderiv ℝ (G F) (s, x) v)
      (fderiv ℝ (fderiv ℝ (G F)) (t, x) (1, 0) v) t := by
    exact (ContinuousLinearMap.apply ℝ Vec v).hasFDerivAt.comp_hasDerivAt t h1
  exact (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t h2

lemma pd_H (hDG : Differentiable ℝ (fderiv ℝ (G F))) (t : ℝ) (x : Vec) (j i : Fin 3) :
    partialDeriv (fun y => fderiv ℝ (G F) (t, y) (1, 0)) j i x =
      fderiv ℝ (fderiv ℝ (G F)) (t, x) (0, EuclideanSpace.single j 1) (1, 0) i := by
  unfold partialDeriv
  have h1 : HasFDerivAt (fun y => fderiv ℝ (G F) (t, y))
      ((fderiv ℝ (fderiv ℝ (G F)) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Vec)) x :=
    (hDG (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  have h2 : HasFDerivAt (fun y => fderiv ℝ (G F) (t, y) (1, 0))
      ((ContinuousLinearMap.apply ℝ Vec ((1 : ℝ), (0 : Vec))).comp
        ((fderiv ℝ (fderiv ℝ (G F)) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Vec))) x :=
    (ContinuousLinearMap.apply ℝ Vec ((1 : ℝ), (0 : Vec))).hasFDerivAt.comp x h1
  rw [h2.fderiv]
  simp

end DTAux

open DTAux in
theorem solution (F : ℝ → Vec → Vec) (hF : SmoothTV F) (t : ℝ) (x : Vec) :
    deriv (fun s => curl (F s) x) t = curl (fun y => deriv (fun s => F s y) t) x := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (G F) := hF
  have hG2 : ContDiff ℝ 2 (G F) := contDiff_infty.mp hG 2
  have hGd : Differentiable ℝ (G F) := hG2.differentiable (by norm_num)
  have hDG : Differentiable ℝ (fderiv ℝ (G F)) :=
    (hG2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hsymm := hG2.contDiffAt (x := (t, x)) |>.isSymmSndFDerivAt (by simp [minSmoothness])
  set D2 := fderiv ℝ (fderiv ℝ (G F)) (t, x)
  -- rewrite the right-hand field
  have hH : (fun y => deriv (fun s => F s y) t) = fun y => fderiv ℝ (G F) (t, y) (1, 0) := by
    funext y; exact (hasDerivAt_F F hGd t y).deriv
  rw [hH]
  -- the left-hand curve, componentwise
  set e : Fin 3 → Vec := fun j => EuclideanSpace.single j 1
  have hcurve : (fun s => curl (F s) x) = fun s =>
      !₂[fderiv ℝ (G F) (s, x) (0, e 1) 2 - fderiv ℝ (G F) (s, x) (0, e 2) 1,
         fderiv ℝ (G F) (s, x) (0, e 2) 0 - fderiv ℝ (G F) (s, x) (0, e 0) 2,
         fderiv ℝ (G F) (s, x) (0, e 0) 1 - fderiv ℝ (G F) (s, x) (0, e 1) 0] := by
    funext s; simp only [curl, pd_F F hGd, e]
  rw [hcurve]
  have hd := fun v i => hasDerivAt_DG F hDG t x v i
  have hvec : HasDerivAt (fun s =>
      (!₂[fderiv ℝ (G F) (s, x) (0, e 1) 2 - fderiv ℝ (G F) (s, x) (0, e 2) 1,
         fderiv ℝ (G F) (s, x) (0, e 2) 0 - fderiv ℝ (G F) (s, x) (0, e 0) 2,
         fderiv ℝ (G F) (s, x) (0, e 0) 1 - fderiv ℝ (G F) (s, x) (0, e 1) 0] : Vec))
      (!₂[D2 (1, 0) (0, e 1) 2 - D2 (1, 0) (0, e 2) 1,
          D2 (1, 0) (0, e 2) 0 - D2 (1, 0) (0, e 0) 2,
          D2 (1, 0) (0, e 0) 1 - D2 (1, 0) (0, e 1) 0]) t := by
    have hpi : HasDerivAt (fun s => ![fderiv ℝ (G F) (s, x) (0, e 1) 2 - fderiv ℝ (G F) (s, x) (0, e 2) 1,
         fderiv ℝ (G F) (s, x) (0, e 2) 0 - fderiv ℝ (G F) (s, x) (0, e 0) 2,
         fderiv ℝ (G F) (s, x) (0, e 0) 1 - fderiv ℝ (G F) (s, x) (0, e 1) 0])
        ![D2 (1, 0) (0, e 1) 2 - D2 (1, 0) (0, e 2) 1,
          D2 (1, 0) (0, e 2) 0 - D2 (1, 0) (0, e 0) 2,
          D2 (1, 0) (0, e 0) 1 - D2 (1, 0) (0, e 1) 0] t := by
      rw [hasDerivAt_pi]
      intro k
      fin_cases k
      · exact (hd _ 2).sub (hd _ 1)
      · exact (hd _ 0).sub (hd _ 2)
      · exact (hd _ 1).sub (hd _ 0)
    exact (PiLp.hasFDerivAt_toLp (p := 2) (𝕜 := ℝ) _).comp_hasDerivAt t hpi
  rw [hvec.deriv]
  simp only [curl, pd_H F hDG t x, e]
  rw [hsymm (1, 0) (0, EuclideanSpace.single 1 1), hsymm (1, 0) (0, EuclideanSpace.single 2 1),
    hsymm (1, 0) (0, EuclideanSpace.single 0 1)]
