-- Prove2me | solution 1 for TaoFivePrimes.rh66388_segment_cut_boundary_20261115
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-14T20:22:54.191971+00:00
-- url     : https://prove2.me/submissions/3a0ef08e-31b6-49a2-ae84-3c74ae684a8b

import Definitions.Def_row23_rh_supp_RH66388CountCapstoneConditional
open Complex
noncomputable section
theorem solution
    (hslab1 : EdgeClearGlue.SlabClear (66388 : ℝ) ((66388 : ℝ) + 3 / 1000))
    (hslab0 : EdgeClearGlue.SlabClear ((121 : ℝ) - 5773 / 100000) 121)
    (hH1 : DiffractionCore.argChangeHoriz riemannZeta (66388 : ℝ) 2 (-1) ∈
      Set.Icc RH66388Count.enclosure.L2.val RH66388Count.enclosure.H2.val)
    (hH0 : DiffractionCore.argChangeHoriz riemannZeta (121 : ℝ) 2 (-1) ∈
      Set.Icc RH66388Count.enclosure.L3.val RH66388Count.enclosure.H3.val)
    (ρ : ℂ) (hz : riemannZeta ρ = 0) (him0 : 0 < ρ.im)
    (himA : (121 : ℝ) ≤ ρ.im) (himB : ρ.im ≤ 66388) : ρ.re = 1 / 2 := by
  exact RH66388Count.segment_of_boundary_inputs hslab1 hslab0 hH1 hH0 ρ hz him0 himA himB
