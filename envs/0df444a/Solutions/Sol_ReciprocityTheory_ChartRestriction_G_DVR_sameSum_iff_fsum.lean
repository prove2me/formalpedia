-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.sameSum_iff_fsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:54:44.458096+00:00
-- url     : https://prove2.me/submissions/5d8a2abf-7c5b-4962-bd0a-2320086f9f32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_apply

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
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    LB.SameSum φ ε φ' ε' ↔ fsum φ ε = fsum φ' ε' := by
  constructor
  · intro h
    ext ψ
    rw [fsum_apply, fsum_apply]
    convert h ψ using 2 <;> simp
  · intro h ψ
    have := congrArg (fun f => f ψ) h
    simp only [fsum_apply] at this
    convert this using 2 <;> simp
end ReciprocityTheory.ChartRestriction.G.DVR
