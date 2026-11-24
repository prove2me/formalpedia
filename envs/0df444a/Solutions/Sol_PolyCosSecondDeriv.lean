-- Prove2me | solution 1 for PolyCosSecondDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:27:51.819803+00:00
-- url     : https://prove2.me/submissions/dc4ce51b-1765-4d48-84e1-5fb73daf22f7

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_PolyCosSecondDeriv

set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution (P : Polynomial ℝ) :
    iteratedDeriv 2 (fun t : ℝ => P.eval (Real.cos t)) 0
      = -(Polynomial.derivative P).eval 1 := by
  have hd1 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Polynomial.eval (Real.cos s) P)
      (-(Real.sin t) * Polynomial.eval (Real.cos t) (Polynomial.derivative P)) t := by
    intro t
    have h := (P.hasDerivAt (Real.cos t)).comp t (Real.hasDerivAt_cos t)
    have hval : Polynomial.eval (Real.cos t) (Polynomial.derivative P) * -Real.sin t
        = -(Real.sin t) * Polynomial.eval (Real.cos t) (Polynomial.derivative P) := by ring
    exact hval ▸ h
  have hG1 : deriv (fun s : ℝ => Polynomial.eval (Real.cos s) P)
      = fun t : ℝ => -(Real.sin t) * Polynomial.eval (Real.cos t) (Polynomial.derivative P) :=
    funext fun t => (hd1 t).deriv
  have hd2 : HasDerivAt
      (fun t : ℝ => -(Real.sin t) * Polynomial.eval (Real.cos t) (Polynomial.derivative P))
      (-(Real.cos 0) * Polynomial.eval (Real.cos 0) (Polynomial.derivative P)
        + -(Real.sin 0)
          * (Polynomial.eval (Real.cos 0)
              (Polynomial.derivative (Polynomial.derivative P)) * -Real.sin 0)) 0 := by
    have hf : HasDerivAt (fun s : ℝ => -(Real.sin s)) (-(Real.cos 0)) 0 :=
      (Real.hasDerivAt_sin 0).neg
    have hg : HasDerivAt
        (fun s : ℝ => Polynomial.eval (Real.cos s) (Polynomial.derivative P))
        (Polynomial.eval (Real.cos 0)
          (Polynomial.derivative (Polynomial.derivative P)) * -Real.sin 0) 0 :=
      ((Polynomial.derivative P).hasDerivAt (Real.cos 0)).comp 0 (Real.hasDerivAt_cos 0)
    exact hf.mul hg
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hG1, hd2.deriv]
  simp
