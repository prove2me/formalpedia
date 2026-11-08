-- Prove2me | solution 1 for WassersteinDRO.GelbrichFiniteSample.eq_17_gelbrich_hull_union
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:11:48.4137+00:00
-- url     : https://prove2.me/submissions/d3b5fecb-0c33-417a-bb0b-18e632bd8db1

import Mathlib
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_chebyshevSet
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_gelbrichHull
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_uncertaintySet

open MeasureTheory

open WassersteinDRO.GelbrichFiniteSample in
theorem solution {m : ℕ} (Ξ : Set (EuclideanSpace ℝ (Fin m))) (ε : ℝ)
    (μh : EuclideanSpace ℝ (Fin m)) (Sigh : Matrix (Fin m) (Fin m) ℝ) (hSigh : Sigh.PosSemidef) :
    gelbrichHull Ξ ε μh Sigh = ⋃ p ∈ uncertaintySet ε μh Sigh, chebyshevSet Ξ p.1 p.2 := by
  ext Q
  simp only [gelbrichHull, chebyshevSet, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨h1, h2, μ, Sig, h3, h4⟩
    exact ⟨(μ, Sig), h4, h1, h2, h3⟩
  · rintro ⟨p, h4, h1, h2, h3⟩
    exact ⟨h1, h2, p.1, p.2, h3, h4⟩
