-- Prove2me | solution 1 for P2M_GlobalTheory_WCub_tri_th__d2b9dc26ad83
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:57:06.109443+00:00
-- url     : https://prove2.me/submissions/e9a48ad8-caac-46eb-ab49-5a8829b610cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TripleProductPointCompProjection
import Theorems.Thm_GlobalTheory_WCub_tripleProductPoint_comp_projection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.WCub
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S S' : Scheme.{0}} {G : Over S} (f : S' ⟶ S) {E T : Over S'} (p : (Over.map f).obj E ⟶ G)
  (x : Fin 3 → (T ⟶ E))
namespace GlobalTheory.WCub
theorem _root_.solution [GrpObj G] [IsCommMonObj G] [GrpObj E] [IsCommMonObj E] (q : E ⟶ (Over.pullback f).obj G)
    [IsMonHom q] (hp : p.left = q.left ≫ pullback.fst G.hom f) (k : thK) :
    tri f p x ≫ thφ G (x3 G) k = (psum E x k.down).left ≫ p.left := by
  have h := isGrpPullback_pullback G f
  have e₁ := psum_push h (fun i => x i ≫ q) (x3 G)
    (lift ((Over.map f).map (x 0) ≫ p) (lift ((Over.map f).map (x 1) ≫ p) ((Over.map f).map (x 2) ≫ p)))
    (fun i => Over.OverMorphism.ext (by
      refine Eq.trans ?_ (tripleProductPoint_comp_projection f p x i).symm
      rw [hp]
      exact Category.assoc _ _ _)) k.down
  have e₂ := psum_hom (MonoidHom.mk' (fun z : T ⟶ E => z ≫ q) fun a b => MonObj.mul_comp a b q) x k.down
  refine e₁.symm.trans ?_
  rw [hp, ← Category.assoc]
  exact congrArg (fun z => z.left ≫ pullback.fst G.hom f) e₂.symm
end GlobalTheory.WCub
