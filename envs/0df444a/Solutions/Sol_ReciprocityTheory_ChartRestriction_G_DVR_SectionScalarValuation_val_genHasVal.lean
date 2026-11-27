-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.val_genHasVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:23:38.88596+00:00
-- url     : https://prove2.me/submissions/015fe725-c243-4c30-b1a4-7849f1063ec9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsRosatiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsValGenHasVal

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
theorem _root_.solution {X : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix]
    {φ : Ix → (Spec (CommRingCat.of V) ⟶ X)} {φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    {hφ : ∀ k, φ' k = jK V ≫ φ k} {ε : Ix → ℤ} {t : LB.Gen (LB.LinComb L φ' ε)}
    {e : LB.Gen (LB.LinComb L φ ε)} {c : FractionRing V}
    (hte : ∀ j, (t.s j).val = resTop _ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) *
      (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j))).val)
    {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of (FractionRing V))) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) :
    (val t r z J).val = gs r z ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) *
      (val e (r ≫ jK V) z J).val := by
  have hz : r z ∈ LB.wchart L φ' (fun k => J (r ≫ φ' k)) := hJ.mem φ' r
  have hj : (fun k => J ((r ≫ jK V) ≫ φ k)) = fun k => J (r ≫ φ' k) := by
    funext k
    rw [hφ k, Category.assoc]
  have hz' : (r ≫ jK V) z ∈ LB.wchart L φ (fun k => J (r ≫ φ' k)) := by
    have := hJ.mem φ (r ≫ jK V)
    rwa [hj] at this
  have he := congrArg (fun j : Ix → L.ι => (gm (r ≫ jK V) z (LB.wchart L φ j) (e.s j)).val) hj
  unfold val
  erw [he, ← gs_unit _ _ _ hz, ← gs_unit _ _ _ hz', hte, gs_mul _ _ _ hz]
  congr 1
  · exact gs_res r z le_top hz _
  · simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
    erw [gs_res r z _ hz, gs_pull r (jK V) z _ hz']
end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
