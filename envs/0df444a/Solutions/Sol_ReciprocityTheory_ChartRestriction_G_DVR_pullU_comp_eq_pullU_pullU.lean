-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.pullU_comp_eq_pullU_pullU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:29:21.645415+00:00
-- url     : https://prove2.me/submissions/3020850b-a897-42af-b20b-fd2ab14093ad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric

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
theorem _root_.solution (h : Z ⟶ Y) (ψ : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) :
    pullU (h ≫ ψ) U x = pullU h (ψ ⁻¹ᵁ U) (pullU ψ U x) := by
  ext
  show ((h ≫ ψ).app U).hom x.val = (h.app _).hom ((ψ.app U).hom x.val)
  first
  | rfl
  | (rw [Scheme.Hom.comp_app]; rfl)
  | simp
end ReciprocityTheory.ChartRestriction.G.DVR
