-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_sameSum_fam_B0_35865ba2bb03
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:35.692451+00:00
-- url     : https://prove2.me/submissions/a88d6c33-07e8-455a-9d36-bb8052dff59a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenRank
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_fam_B0_one_2c33f401c32a
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_fam_B0_two_7d24f9aa1259

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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I)
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution : LB.SameSum (D.toPre.famφB 0) (DegPre.famε 1)
    (fun _ : Fin 1 => 𝟙 D.toPre.P.A.left) (fun _ => ((1 : ℕ) : ℤ)) := by
  intro ψ
  have h0 : D.toPre.famφB 0 0 = 𝟙 _ := rfl
  have e1 := famφB0_one D
  have e2 := famφB0_two D
  rw [Fin.sum_univ_four, Fin.sum_univ_one]
  split_ifs
  all_goals first
    | (exfalso; exact ‹¬ 𝟙 D.toPre.P.A.left = ψ› (h0.symm.trans ‹D.toPre.famφB 0 0 = ψ›))
    | (exfalso; exact ‹¬ D.toPre.famφB 0 0 = ψ› (h0.trans ‹𝟙 D.toPre.P.A.left = ψ›))
    | (exfalso; exact ‹¬ 𝟙 D.toPre.P.A.left = ψ› (e1.symm.trans ‹D.toPre.famφB 0 1 = ψ›))
    | (exfalso; exact ‹¬ D.toPre.famφB 0 1 = ψ› (e1.trans ‹𝟙 D.toPre.P.A.left = ψ›))
    | (exfalso; exact ‹¬ D.toPre.famφB 0 3 = ψ› (e2.symm.trans ‹D.toPre.famφB 0 2 = ψ›))
    | (exfalso; exact ‹¬ D.toPre.famφB 0 2 = ψ› (e2.trans ‹D.toPre.famφB 0 3 = ψ›))
    | (simp [DegPre.famε]; done)
    | rfl
    | decide
end ReciprocityTheory.ChartRestriction.G.DVR.TG
