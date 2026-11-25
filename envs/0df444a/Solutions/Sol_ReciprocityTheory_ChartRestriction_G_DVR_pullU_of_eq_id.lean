-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.pullU_of_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:25.556356+00:00
-- url     : https://prove2.me/submissions/32c76c7e-3acf-42e7-9fa8-2e1f6c2aa0f7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric

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
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (f : Z ⟶ Z) (hf : f = 𝟙 Z) (U V : Z.Opens) (hV : V ≤ f ⁻¹ᵁ U) (hV' : V ≤ U)
    (c : Γ(Z, U)ˣ) : res hV (pullU f U c) = res hV' c := by
  subst hf
  ext
  simp [res, pullU, CommRingCat.hom_id, Units.coe_map] <;> rfl
end ReciprocityTheory.ChartRestriction.G.DVR
