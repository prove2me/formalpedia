-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_zero_gt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:10.828597+00:00
-- url     : https://prove2.me/submissions/c031f0a2-78a5-4f4e-9a1f-67c106815c2c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isZero_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
private lemma th_eq_one' {y : (TF (R := R) F).left} {J} (hJ : Good D.P.L y J)
    (x x' : TF (R := R) F ⟶ D.P.A) : th D y J x x' 1 = 1 := by
  have hm : lift x (lift x' 1) = lift x x' ≫ faceMap (G := D.P.A) 2 := by
    simp [faceMap, x2, pzero, Hom.one_def]
  refine Eq.trans ?_ ((val_corr (hJ := hJ) (D.cub.face 2) (lift x x').left).trans (val_one _))
  refine Eq.trans ?_ (val_pull (hJ := hJ) ..).symm
  show val D.cub.t (lift x (lift x' 1)).left y J = _
  rw [hm, Over.comp_left]
  all_goals rfl
variable {O : Type} [CommRing O] [StarRing O] [Module O D.X]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution : ∃ g : GtPtF D F, g.IsZero := by
  have hgen : (LB.oneGen D.P.L (Y := (TF (R := R) F).left)).IsGen := by
    intro i j
    first
    | exact (_root_.one_mul _).symm
    | (simp only [LB.oneGen, LB.LinComb, Finset.univ_eq_empty, Finset.prod_empty]
       exact (_root_.one_mul _).symm)
    | (simp [LB.oneGen, LB.LinComb]
       rw [_root_.one_mul])
  obtain ⟨g, hb, hg⟩ := exists_gt (D := D) (F := F) (1 : TF (R := R) F ⟶ D.P.A) (K := PEmpty)
    (φ := fun _ => PEmpty.elim) (ε := PEmpty.elim) (fun _ => LB.oneGen D.P.L) (fun _ => hgen)
    (fun χ => by
      intro U _ h
      rw [prod_gt]
      simp)
    (fun y J _ => val_one _)
    (fun χ χ' y J hy => by
      rw [th_eq_one' hy]
      congr 1
      exact (val_one _).symm)
  exact ⟨g, (isZero_iff g).2 ⟨hb, fun χ y J hy => (hg χ y J hy).trans (val_one _)⟩⟩
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
