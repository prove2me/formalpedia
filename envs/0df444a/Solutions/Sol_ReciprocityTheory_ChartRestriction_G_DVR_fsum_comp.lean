-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.fsum_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:05.05885+00:00
-- url     : https://prove2.me/submissions/dceb50af-de35-46a0-b4a3-9134a0e8fecf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped Classical
variable {X Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) {Z : Scheme.{0}} (h : Z ⟶ Y) :
    fsum (fun k => h ≫ φ k) ε = Finsupp.mapDomain (fun ψ => h ≫ ψ) (fsum φ ε) := by
  simp [fsum, Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_single]
end ReciprocityTheory.ChartRestriction.G.DVR
