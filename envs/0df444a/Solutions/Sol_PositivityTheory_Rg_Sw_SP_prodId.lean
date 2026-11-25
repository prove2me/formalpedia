-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.prodId
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:57:21.937936+00:00
-- url     : https://prove2.me/submissions/290106da-5824-41e6-ba5f-65d373d0812b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorIter
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.SP.Mi
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (a : Polynomial ℂ) (c : ℂ) (ρ N : ℕ) :
    Polynomial.C (((-c) ^ ρ) ^ N) * ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (a + (l : Polynomial ℂ) - (i : Polynomial ℂ)) =
      Polynomial.C ((c ^ ρ) ^ N) * ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (-a - Polynomial.C ((l : ℂ) - i)) := by
  have e : ∀ l i : ℕ, (-a - Polynomial.C ((l : ℂ) - i)) = (-1) * (a + (l : Polynomial ℂ) - (i : Polynomial ℂ)) := by
    intro l i
    simp only [map_sub, map_natCast]
    ring
  simp_rw [e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  simp only [map_pow, map_neg]
  ring
end PositivityTheory.Rg.Sw.SP
