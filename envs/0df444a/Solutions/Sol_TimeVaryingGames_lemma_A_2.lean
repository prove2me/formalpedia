-- Prove2me | solution 1 for TimeVaryingGames.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:24:59.891729+00:00
-- url     : https://prove2.me/submissions/46de5734-7995-4619-b2bc-fa881fe59d09

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF

open TimeVaryingGames in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} {Kc : ℝ} {h : E → ℝ} {gradh : E → E →L[ℝ] ℝ} (hdgf : IsDGF C Kc h gradh)
    {p : E} (hp : p ∈ C) {x x' : E} (hx : x ∈ proxDomain C h) (hx' : x' ∈ proxDomain C h) :
    bregman h gradh p x =
      bregman h gradh p x' + bregman h gradh x' x + (gradh x - gradh x') (x' - p) := by
  simp only [bregman, ContinuousLinearMap.sub_apply, map_sub]
  ring
