-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_finset__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:19:38.235568+00:00
-- url     : https://prove2.me/submissions/709f0d78-53f3-4ae1-9354-5dff943035d1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (W : Finset V) :
    WilliamsonShmoys.HasPlanarDrawingOn (M.induce (W : Set V)) := by
  classical
  rcases hM with ⟨p, arc, hp, hcurve, hcross⟩
  let p' : W → ℝ × ℝ := fun u => p u.val
  let arc' : W → W → ℝ → ℝ × ℝ := fun u v t => arc u.val v.val t
  refine ⟨p', arc', ?_, ?_, ?_⟩
  · intro u v huv
    apply Subtype.ext
    apply hp
    simpa [p'] using huv
  · intro u v huv hadj
    have huv' : u.val < v.val := huv
    have hadj' : M.Adj u.val v.val := by simpa using hadj
    rcases hcurve u.val v.val huv' hadj' with ⟨hcont, hinj, hzero, hone, havoid⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [arc'] using hcont
    · simpa [arc'] using hinj
    · simpa [arc', p'] using hzero
    · simpa [arc', p'] using hone
    · intro t ht w hw
      exact (havoid t ht w.val) (by simpa [arc', p'] using hw)
  · intro u v x y huv hxy hadjuv hadjxy hne
    have huv' : u.val < v.val := huv
    have hxy' : x.val < y.val := hxy
    have hadjuv' : M.Adj u.val v.val := by simpa using hadjuv
    have hadjxy' : M.Adj x.val y.val := by simpa using hadjxy
    have hne' : (u.val, v.val) ≠ (x.val, y.val) := by
      intro heq
      apply hne
      exact Prod.ext (Subtype.ext (congrArg Prod.fst heq))
        (Subtype.ext (congrArg Prod.snd heq))
    simpa [arc'] using
      hcross u.val v.val x.val y.val huv' hxy' hadjuv' hadjxy' hne'