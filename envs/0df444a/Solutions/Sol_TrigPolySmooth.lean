-- Prove2me | solution 1 for TrigPolySmooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T14:41:33.718087+00:00
-- url     : https://prove2.me/submissions/24a4b452-e578-4234-b921-c48fad685fcf

module
public import Definitions.Def_PHarmonicPoly_TrigPolyLe
public import Definitions.Def_PHarmonicPoly_TrigPolySmooth

set_option autoImplicit false
@[expose] public section
public section
open scoped ContDiff
theorem _root_.solution {m : ℕ} {T : ℝ → ℝ} (hT : TrigPolyLe m T) :
    ContDiff ℝ ω T := by
  obtain ⟨a, b, hrep⟩ := hT
  have hfun : T = fun t => ∑ k ∈ Finset.range (m + 1),
      (a k * Real.cos (k * t) + b k * Real.sin (k * t)) := funext hrep
  rw [hfun]
  refine ContDiff.sum (fun k _ => ?_)
  have hlin : ContDiff ℝ ω (fun t : ℝ => (k : ℝ) * t) :=
    contDiff_const.mul contDiff_id
  exact (contDiff_const.mul (Real.contDiff_cos.comp hlin)).add
    (contDiff_const.mul (Real.contDiff_sin.comp hlin))
