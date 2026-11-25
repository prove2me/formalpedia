-- Prove2me | solution 1 for P2M_GlobalTheory_LamBiext_formEq__87630df18372
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:31:45.433505+00:00
-- url     : https://prove2.me/submissions/599c23da-b007-40b2-8d13-eb49f4f845d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_MulGenNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLaws
import Theorems.Thm_GlobalTheory_LamBiext_prod_lam
import Theorems.Thm_P2M_GlobalTheory_LamBiext_prod_law__e869053602e8
import Theorems.Thm_P2M_GlobalTheory_LamBiext_id__807418007fce
import Theorems.Thm_GlobalTheory_LamBiext_prod_flat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LamBiext
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.LamBiext
theorem _root_.solution : FormEq (thφ G (x3 G)) thε
    (flatφ (lamφ G) (law1φ G (x3 G 0) (x3 G 1) (x3 G 2))) (flatε lamε lawε) := fun U _ h => by
  have a := prod_cub (x3 G 0) (x3 G 1) (x3 G 2) h
  rw [id₃] at a
  simp only [Over.id_left, Category.id_comp] at a
  have b := prod_law₁ (x3 G 0) (x3 G 1) (x3 G 2) (fun χ => ∏ i, h (χ ≫ lamφ G i) ^ lamε i)
  rw [id₃] at b
  simp only [Over.id_left, Category.id_comp, prod_lam] at b
  rw [a, prod_flat, b]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.LamBiext
