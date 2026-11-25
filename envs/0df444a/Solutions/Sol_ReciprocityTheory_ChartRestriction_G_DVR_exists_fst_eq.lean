-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.exists_fst_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:03.561405+00:00
-- url     : https://prove2.me/submissions/e7e7e0e6-51b2-44ae-a588-000870ce0b0a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThickKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_NuExtA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {X : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (p : X ⟶ Sp V) (J : Ideal V) {r : V} (hJ : J ≤ Ideal.span {r}) (x : X)
    (hx : r ∈ (p x).asIdeal) :
    ∃ x', pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) x' = x := by
  have h1 : x ∈ Set.range (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) := by
    rw [Scheme.Pullback.range_fst]
    show p x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J))
    rw [range_comap_of_surjective (V ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact fun y hy => (Ideal.span_singleton_le_iff_mem _).2 hx (hJ hy)
  exact h1
end ReciprocityTheory.ChartRestriction.G.DVR
