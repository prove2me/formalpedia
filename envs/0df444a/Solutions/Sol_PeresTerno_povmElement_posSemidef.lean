-- Prove2me | solution 1 for PeresTerno.povmElement_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:25:47.228348+00:00
-- url     : https://prove2.me/submissions/61b740b5-7f03-4343-bf98-9b23c6124ac7

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix
open scoped ComplexOrder

open PeresTerno Matrix ComplexOrder in
theorem solution {d e ι : Type*} [Fintype d] [Fintype e] [Fintype ι]
    (A : ι → Matrix e d ℂ) :
    (povmElement A).PosSemidef := by
  unfold povmElement
  classical
  exact Matrix.posSemidef_sum Finset.univ (fun m _ => Matrix.posSemidef_conjTranspose_mul_self (A m))
