-- Prove2me | solution 1 for P2M_GlobalTheory_PullUnifHom_valAt__pull_g__975f6bbd66e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:31:44.770033+00:00
-- url     : https://prove2.me/submissions/61be9ac3-f3f2-49ed-a358-555e0addd290

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHolUnifPullAlongGroupHom
import Theorems.Thm_P2M_GlobalTheory_PullUnifHom_chart_pull_iff__be1866fa7be3
import Theorems.Thm_P2M_GlobalTheory_PullUnifHom_le_left__12395fff6ef7
import Theorems.Thm_P2M_GlobalTheory_PullUnifHom_le_right__76c8cd51ee71
import Theorems.Thm_GlobalTheory_PullHermitian_unitVal_linComb
import Theorems.Thm_P2M_GlobalTheory_PullHermitian_valAt__eq_unitVal_3711952a0e7e


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.PullUnifHom
open GlobalTheory.PullHermitian
variable {X Y : Scheme.{0}}
namespace GlobalTheory.PullUnifHom
theorem _root_.solution (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (i j : PUnit → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.pull f).U i ⊓ (L.pull f).U j)) :
    valAt' x ((L.pull f).U i ⊓ (L.pull f).U j) ((L.pull f).g i j).val =
      valAt' (x ≫ f) (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))
        (L.g (i PUnit.unit) (j PUnit.unit)).val := by
  have hi := (chart_pull_iff' x L f i).1 (le_left' h)
  have hj := (chart_pull_iff' x L f j).1 (le_right' h)
  rw [valAt'_eq_unitVal x h, valAt'_eq_unitVal _ (inf_of _ hi hj)]
  have := unitVal_linComb x L f 1 (i PUnit.unit) (j PUnit.unit) h (inf_of _ hi hj)
  exact congrArg Units.val (this.trans (zpow_one _))
end GlobalTheory.PullUnifHom
