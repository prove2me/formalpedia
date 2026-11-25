-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.hasGen_lam_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:17:21.374825+00:00
-- url     : https://prove2.me/submissions/14758aed-08bc-4b4c-9436-c2fcda1af220

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasGen_theta
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lambdaMap_one_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zero


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
variable {M : LB A.left}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (t : LB.Gen (Theta A M)) (ht : t.IsGen) (x y : T ⟶ A) :
    ∀ n : ℕ, HasGen M (lf (lamP x (y ^ n) - (n : ℤ) • lamP x y))
  | 0 => by simpa [lambdaMap_one_eq_zero, lf] using (HasGen.zero (L := M))
  | n + 1 => by
    have h := (hasGen_theta t ht x (y ^ n) y).add (solution t ht x y n)
    rw [← lf_add] at h
    convert h using 2
    rw [pow_succ]
    simp only [Nat.cast_succ, add_smul, one_smul]
    abel
end ReciprocityTheory.ChartRestriction.G.DVR
