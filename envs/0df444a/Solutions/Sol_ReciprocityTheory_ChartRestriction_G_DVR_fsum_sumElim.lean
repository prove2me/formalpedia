-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.fsum_sumElim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:40.065867+00:00
-- url     : https://prove2.me/submissions/72943d6b-e4cc-4784-9a80-0b56eceb1e24

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
theorem _root_.solution {K₂ : Type} [Fintype K₂] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) :
    fsum (Sum.elim φ φ₂) (Sum.elim ε ε₂) = fsum φ ε + fsum φ₂ ε₂ := by
  simp [fsum, Fintype.sum_sum_type]
end ReciprocityTheory.ChartRestriction.G.DVR
