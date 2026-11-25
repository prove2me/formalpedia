-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.quotient_mk_mul_congr_colon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:46:13.713462+00:00
-- url     : https://prove2.me/submissions/139c3ca2-72b3-4cfb-b52a-12ba1bc68b4b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqSumMultihomogeneousComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {F q : Ideal (MRing ι)} {f : MRing ι} (hq : ∀ g, g ∈ q ↔ g * f ∈ F)
    {g g' : MRing ι} (h : Ideal.Quotient.mk q g = Ideal.Quotient.mk q g') :
    Ideal.Quotient.mk F (g * f) = Ideal.Quotient.mk F (g' * f) := by
  rw [Ideal.Quotient.eq] at h ⊢
  rw [← sub_mul]
  exact (hq _).1 h
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
