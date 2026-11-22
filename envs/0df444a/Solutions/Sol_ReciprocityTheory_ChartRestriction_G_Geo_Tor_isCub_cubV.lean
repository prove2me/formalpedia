-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.isCub_cubV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:44:17.240382+00:00
-- url     : https://prove2.me/submissions/412ccc73-97f8-4add-b76d-43afc72d06da

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {T : Over S} {z : T.left} {J : (T.left ⟶ G.left) → L.L.ι} (hJ : Good L.L z J) : IsCub (cubV c z J) where
  face x y := by
    have := val_corr hJ (c.face 0) (lift x y).left
    rw [val_one] at this
    refine Eq.trans ?_ this
    refine Eq.trans ?_ (val_cub c (lift x y) hJ (pzero G _) (x2 G 0) (x2 G 1)).symm
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  s01 x y w := by
    have := (val_corr hJ c.cubeSymmetric_swap_first (lift x (lift y w)).left).trans (val_cub c (lift x (lift y w)) hJ _ _ _)
    refine Eq.trans this ?_
    congr 1 <;> simp [x3]
  s12 x y w := by
    have := (val_corr hJ c.cubeSymmetric_swap_last (lift x (lift y w)).left).trans (val_cub c (lift x (lift y w)) hJ _ _ _)
    refine Eq.trans this ?_
    congr 1 <;> simp [x3]
  coc x x' x'' y := by
    have := val_corr hJ c.cocycle (lift x (lift x' (lift x'' y))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c _ hJ _ _ _) (val_cub c _ hJ _ _ _))).symm.trans
      (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_cub c _ hJ _ _ _) (val_cub c _ hJ _ _ _))))
    have a₀ : lift x (lift x' (lift x'' y)) ≫ x4 G 0 = x := by simp [x4]
    have a₁ : lift x (lift x' (lift x'' y)) ≫ x4 G 1 = x' := by simp [x4]
    have a₂ : lift x (lift x' (lift x'' y)) ≫ x4 G 2 = x'' := by simp [x4]
    have a₃ : lift x (lift x' (lift x'' y)) ≫ x4 G 3 = y := by simp [x4]
    have b₀ : lift x (lift x' (lift x'' y)) ≫ padd G (x4 G 0) (x4 G 1) = x * x' :=
      (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
    have b₁ : lift x (lift x' (lift x'' y)) ≫ padd G (x4 G 1) (x4 G 2) = x' * x'' :=
      (MonObj.comp_mul _ _ _).trans (by rw [a₁, a₂])
    rwa [b₀, b₁, a₀, a₁, a₂, a₃] at e
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
