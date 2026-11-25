-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.rFac_zero_pf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:01:31.649104+00:00
-- url     : https://prove2.me/submissions/85cf3247-e4ce-4c89-a594-90db030898e4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValuePf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rv_c_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rv_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rv_val_tau_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
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
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (oa : D.toPre.OAct O) (a : O)
    (uR : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (huR : uR.IsGen)
    (hn : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ uR (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (χ : D.toPre.X) :
    LB.Gen.Corr D.toPre.P.L _ _ (K' := PEmpty) PEmpty.elim PEmpty.elim
      (LB.pullGen D.toPre.P.L _ _ (rFac D F oa a uR χ) (DegPre.zF D.toPre F).left) (LB.oneGen D.toPre.P.L) := by
  have hL := D.toPre.P.isLB
  have hb := oa.tau_bal (star a)
  rw [star_star] at hb
  refine corr_of_val hL fun y J hJ => ?_
  unfold rFac
  rw [val_pull hJ, val_pull hJ, val_one]
  have hc := val_corr hJ (hb uR huR hn χ 0) (jFK (R := V) F)
  simp only at hc
  have h0 : a • (0 : D.toPre.X) = 0 := smul_zero a
  rw [h0] at hc
  rw [val_mul hJ, val_pull hJ, rv_val_tau_zero _ _ _ hJ, rv_val_tau_zero _ _ _ hJ] at hc
  have hm : (𝟙 _ ≫ (DegPre.zF D.toPre F).left) ≫ (lift (cPB D F χ) (DegPre.prB D.toPre F)).left =
      jFK (R := V) F ≫ D.toPre.pt2 χ 0 := by
    have z₁ : DegPre.zF D.toPre F ≫ cPB D F χ = toUnit _ ≫ D.toPre.c χ := by
      rw [cPB, ← Category.assoc, comp_toUnit]
    have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
    rw [Category.id_comp, ← Over.comp_left, comp_lift, z₁, z₂, ← rv_pt, rv_c_zero, MonObj.comp_one]
  rw [hm]
  exact mul_eq_left.1 hc
end ReciprocityTheory.ChartRestriction.G.DVR
