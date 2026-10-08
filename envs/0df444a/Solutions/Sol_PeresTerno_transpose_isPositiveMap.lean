-- Prove2me | solution 1 for PeresTerno.transpose_isPositiveMap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:46:25.788383+00:00
-- url     : https://prove2.me/submissions/7102040a-f97e-4bd6-b0ad-eaf6f7509933

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix
open scoped ComplexOrder

open PeresTerno Matrix ComplexOrder in
theorem solution {d : Type*} [Fintype d] :
    IsPositiveMap (fun ρ : Matrix d d ℂ => ρᵀ) := by
  intro ρ hρ
  exact hρ.transpose
