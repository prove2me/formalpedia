-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.exists_uR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:07:39.61652+00:00
-- url     : https://prove2.me/submissions/8e2cf140-11c1-436b-97e7-8758d7a66c7d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsAtScale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_normalized_to
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_empty
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_of_local_base
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_padd_eq_mul


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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (D : DegData V (maximalIdeal V)) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
    (oa : D.toPre.OAct O) (a : O) :
    ∃ uR : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε),
      uR.IsGen ∧
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uR (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L) := by
  have hL : D.toPre.P.L.IsLB := D.toPre.P.isLB
  have hA := oa.onB.rosati (star a)
  rw [star_star] at hA
  obtain ⟨u0, hu0⟩ := gen_of_local_base hL (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε hA
  have hzp : zero2 D.toPre.P.A ≫ (toUnit (D.toPre.P.A ⊗ D.toPre.P.A)).left = 𝟙 _ := by
    simp only [zero2, ← Over.comp_left]
    rw [show _ ≫ toUnit (D.toPre.P.A ⊗ D.toPre.P.A) = 𝟙 _ from toUnit_unique _ _]
    rfl
  have hone : (LB.oneGen D.toPre.P.L (Y := (𝟙_ (Over (Spec (CommRingCat.of V)))).left)).IsGen := by
    intro i j
    show res _ 1 = _ * res _ 1
    rw [map_one, map_one, _root_.mul_one]
    simp [LB.LinComb]
    rfl
  refine exists_normalized_to hL _ _ u0 hu0 _ _ hzp _ _ _ hone ?_
  haveI := oa.onB.hom (star a)
  haveI := oa.onB.hom a
  have e : (fun k => zero2 D.toPre.P.A ≫ rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a) k) =
      fun _ => (η[D.toPre.P.A]).left := by
    funext i
    have h1 : (η[D.toPre.P.A] : 𝟙_ _ ⟶ D.toPre.P.A) = 1 := by rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have hm : (1 : 𝟙_ _ ⟶ D.toPre.P.A) * 1 = 1 := _root_.mul_one _
    fin_cases i
    · show (lift η[D.toPre.P.A] η[D.toPre.P.A]).left ≫
        (padd D.toPre.P.A (fst _ _ ≫ oa.onB.act (star a)) (snd _ _)).left = _
      rw [← Over.comp_left, padd_eq_mul, MonObj.comp_mul, lift_fst_assoc, lift_snd, IsMonHom.one_hom, h1, hm]
    · show (lift η[D.toPre.P.A] η[D.toPre.P.A]).left ≫ (fst _ _ ≫ oa.onB.act (star a)).left = _
      rw [← Over.comp_left, lift_fst_assoc, IsMonHom.one_hom]
    · show (lift η[D.toPre.P.A] η[D.toPre.P.A]).left ≫ (snd D.toPre.P.A D.toPre.P.A).left = _
      rw [← Over.comp_left, lift_snd]
    · show (lift η[D.toPre.P.A] η[D.toPre.P.A]).left ≫
        (padd D.toPre.P.A (fst _ _) (snd _ _ ≫ oa.onB.act a)).left = _
      rw [← Over.comp_left, padd_eq_mul, MonObj.comp_mul, lift_fst, lift_snd_assoc, IsMonHom.one_hom, h1, hm]
    · show (lift η[D.toPre.P.A] η[D.toPre.P.A]).left ≫ (fst D.toPre.P.A D.toPre.P.A).left = _
      rw [← Over.comp_left, lift_fst]
    · show (lift η[D.toPre.P.A] η[D.toPre.P.A]).left ≫ (snd _ _ ≫ oa.onB.act a).left = _
      rw [← Over.comp_left, lift_snd_assoc, IsMonHom.one_hom]
  rw [fsum_empty, e]
  simp [fsum, Fin.sum_univ_six, rosatiε, ← Finsupp.single_add]
end ReciprocityTheory.ChartRestriction.G.DVR
