-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.GC.exists_chart_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:07:34.617037+00:00
-- url     : https://prove2.me/submissions/5427307c-3a47-41c1-82fd-46875940a1bc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.GC
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.DVR.GC
theorem _root_.solution {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    (q : Spec (CommRingCat.of V) ⟶ X) : ∃ i, q ⁻¹ᵁ L.U i = ⊤ := by
  obtain ⟨i, hi⟩ : ∃ i, q.base (IsLocalRing.closedPoint V) ∈ L.U i := by
    have : q.base (IsLocalRing.closedPoint V) ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  refine ⟨i, top_unique fun x _ => ?_⟩
  have hs : x ⤳ IsLocalRing.closedPoint V :=
    (PrimeSpectrum.le_iff_specializes x _).1 (IsLocalRing.le_maximalIdeal x.isPrime.ne_top)
  exact hs.mem_open (q ⁻¹ᵁ L.U i).isOpen hi
end ReciprocityTheory.ChartRestriction.G.DVR.GC
