-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.scaleGen_isGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:53:49.115751+00:00
-- url     : https://prove2.me/submissions/1a492ffc-ebdd-4980-b1f3-54b732cc2eb8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
private lemma res_res_lemma {S : Scheme.{0}} {U V W : S.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(S, U)ˣ) :
    res h2 (res h1 x) = res (h2.trans h1) x := by
  have hc : S.presheaf.map (homOfLE h1).op ≫ S.presheaf.map (homOfLE h2).op =
      S.presheaf.map (homOfLE (h2.trans h1)).op := by
    rw [← Functor.map_comp]
    rfl
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← hc]
  rfl
end ReciprocityTheory.ChartRestriction.G.DVR
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {M : LB Y} (c : Γ(Y, ⊤)ˣ) (t : LB.Gen M) (ht : t.IsGen) : (scaleGen c t).IsGen := by
  intro i j
  simp only [scaleGen, map_mul]
  rw [ht i j, res_res_lemma, res_res_lemma, mul_left_comm]
end ReciprocityTheory.ChartRestriction.G.DVR
