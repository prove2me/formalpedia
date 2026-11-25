-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.fsum_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:10.441789+00:00
-- url     : https://prove2.me/submissions/9cf8def4-2a0e-4e1b-8d64-9187ec178254

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
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : Y ⟶ X) :
    fsum φ ε ψ = ∑ k, if φ k = ψ then ε k else 0 := by
  simp only [fsum, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
end ReciprocityTheory.ChartRestriction.G.DVR
