-- Prove2me | solution 1 for TrigPolyDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:41:18.56288+00:00
-- url     : https://prove2.me/submissions/89820652-60a3-44f6-a0c1-1d76c042caa1

module
public import Definitions.Def_PHarmonicPoly_TrigPolyLe
public import Definitions.Def_PHarmonicPoly_TrigPolySmooth
public import Definitions.Def_PHarmonicPoly_TrigPolyDeriv
public import Theorems.Thm_TrigPolySmooth


set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution {m : ℕ} {T : ℝ → ℝ} (hT : TrigPolyLe m T) :
    TrigPolyLe m (deriv T) := by
  obtain ⟨a, b, hrep⟩ := hT
  have hfun : T = fun t => ∑ k ∈ Finset.range (m + 1),
      (a k * Real.cos (k * t) + b k * Real.sin (k * t)) := funext hrep
  refine ⟨fun k => (k : ℝ) * b k, fun k => -((k : ℝ) * a k), fun t => ?_⟩
  have hterm : ∀ k ∈ Finset.range (m + 1),
      HasDerivAt (fun s : ℝ => a k * Real.cos ((k : ℝ) * s) + b k * Real.sin ((k : ℝ) * s))
        ((k : ℝ) * b k * Real.cos ((k : ℝ) * t)
          + -((k : ℝ) * a k) * Real.sin ((k : ℝ) * t)) t := by
    intro k _
    have hlin : HasDerivAt (fun s : ℝ => (k : ℝ) * s) ((k : ℝ)) t := by
      simpa using (hasDerivAt_id t).const_mul ((k : ℝ))
    have hc : HasDerivAt (fun s : ℝ => Real.cos ((k : ℝ) * s))
        (-Real.sin ((k : ℝ) * t) * (k : ℝ)) t := (Real.hasDerivAt_cos _).comp t hlin
    have hs : HasDerivAt (fun s : ℝ => Real.sin ((k : ℝ) * s))
        (Real.cos ((k : ℝ) * t) * (k : ℝ)) t := (Real.hasDerivAt_sin _).comp t hlin
    have hadd := (hc.const_mul (a k)).add (hs.const_mul (b k))
    have hval : a k * (-Real.sin ((k : ℝ) * t) * (k : ℝ))
          + b k * (Real.cos ((k : ℝ) * t) * (k : ℝ))
        = (k : ℝ) * b k * Real.cos ((k : ℝ) * t)
          + -((k : ℝ) * a k) * Real.sin ((k : ℝ) * t) := by ring
    exact hval ▸ hadd
  have hfe : (∑ k ∈ Finset.range (m + 1),
        fun s : ℝ => a k * Real.cos ((k : ℝ) * s) + b k * Real.sin ((k : ℝ) * s))
      = fun s : ℝ => ∑ k ∈ Finset.range (m + 1),
        (a k * Real.cos ((k : ℝ) * s) + b k * Real.sin ((k : ℝ) * s)) := by
    funext s; simp
  have hsum := hfe ▸ HasDerivAt.sum hterm
  rw [hfun]
  exact hsum.deriv
