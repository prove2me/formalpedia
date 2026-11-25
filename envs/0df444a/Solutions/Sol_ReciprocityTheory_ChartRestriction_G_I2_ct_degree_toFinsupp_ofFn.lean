-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ct_degree_toFinsupp_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:10:08.749433+00:00
-- url     : https://prove2.me/submissions/0c98878a-9489-42a1-8b67-309e650d1895

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {ι : Type} [DecidableEq ι] (j : ℕ) (v : Fin j → ι) :
    (Multiset.toFinsupp (↑(List.ofFn v) : Multiset ι)).degree = j := by
  have h := Finsupp.card_toMultiset (Multiset.toFinsupp (↑(List.ofFn v) : Multiset ι))
  rw [Multiset.toFinsupp_toMultiset, Multiset.coe_card, List.length_ofFn] at h
  refine Eq.trans ?_ h.symm
  first
    | rfl
    | simp [Finsupp.degree, Finsupp.sum]
    | simp [Finsupp.degree_eq_sum, Finsupp.sum]
end ReciprocityTheory.ChartRestriction.G.I2
