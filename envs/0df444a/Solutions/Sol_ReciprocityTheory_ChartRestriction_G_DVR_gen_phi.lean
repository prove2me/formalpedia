-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.gen_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:55:26.827791+00:00
-- url     : https://prove2.me/submissions/15fa841d-0cd0-4a4f-a6a7-aaebb8cd82aa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_u
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
variable {D F}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen) (α : D.X) :
    (∃ u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k)), u.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w)) ∧
    ∀ u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k)), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) →
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
        val u ρ.left z J = uVal D F k α p.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (ρ ≫ fst _ _).left z J :=
  gen_u D F hG k α (α + p.y) p.g.b (by rw [cPoint_add, cPoint_y]) _ (mulGen_isGen _ _ _ _ _ _ _ (p.g.isGen α) hw) (fun U _ h => by
    refine (Fintype.prod_sum_type _).trans ?_
    rw [Fin.prod_univ_four, Fin.prod_univ_two]
    show h (cP D _ α * p.g.b).left ^ (-1 : ℤ) * h (cP D _ α).left ^ (1 : ℤ) * h p.g.b.left ^ (1 : ℤ) *
      h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) *
      (h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h p.g.b.left ^ (-(k : ℤ))) = _
    simp only [zpow_neg, zpow_one, zpow_natCast]
    ac_rfl)
end ReciprocityTheory.ChartRestriction.G.DVR
