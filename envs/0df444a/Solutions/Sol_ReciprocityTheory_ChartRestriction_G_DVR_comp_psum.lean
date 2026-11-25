-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.comp_psum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:47:57.533606+00:00
-- url     : https://prove2.me/submissions/74c169a6-f284-44b2-9b05-bc5030ec813a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_padd_eq_mul

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {n : ℕ} (h : T' ⟶ T) (x : Fin n → (T ⟶ A)) (I : Finset (Fin n)) :
    h ≫ psum A x I = psum A (fun k => h ≫ x k) I := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact MonObj.comp_one h
  | cons k l ih =>
    simp only [List.foldr_cons]
    rw [padd_eq_mul, padd_eq_mul, MonObj.comp_mul, ih]
end ReciprocityTheory.ChartRestriction.G.DVR
