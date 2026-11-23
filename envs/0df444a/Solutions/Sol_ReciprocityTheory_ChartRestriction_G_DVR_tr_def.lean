-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.tr_def
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:20.63784+00:00
-- url     : https://prove2.me/submissions/9b7c8792-c359-4519-85a2-136cc8acc1f1

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
variable {X Y : Scheme.{0}} (L : LB X)
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {V : Y.Opens} {ψ : Y ⟶ X} {a b : L.ι} (h : V ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b)) :
    tr L V ψ a b = res h (pullU ψ _ (L.g a b)) := by
  simp [tr, h]
end ReciprocityTheory.ChartRestriction.G.DVR
