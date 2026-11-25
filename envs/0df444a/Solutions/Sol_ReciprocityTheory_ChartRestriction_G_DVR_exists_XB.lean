-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.exists_XB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:20:16.82098+00:00
-- url     : https://prove2.me/submissions/90bcddc7-7f35-4e82-9725-f76f15cf96a5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_of_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_normalized_to
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_of_local_base
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasGen_pullMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_powGen_isGen_of_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen_of_isGen


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
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hL : D.toPre.P.L.IsLB) (oa : D.toPre.OAct O) (w0 : O)
    (uΨ : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4)
      ![(padd D.toPre.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.toPre.P.A.left, (oa.onB.act w0).left,
        (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left] ![1, -2, -1, 2]))
    (huΨ : uΨ.IsGen) (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ) :
    ∃ X : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, (oa.onB.act a).left]
        ![((k * N : ℕ) : ℤ), -(k : ℤ)]), X.IsGen ∧
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ X (eSec D.toPre.P.A))
        (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rig (k * (N - 1))) := by
  have hA := oa.onB.rosati a
  obtain ⟨uR, huR⟩ := gen_of_local_base hL (Out.rosatiφ D.toPre.P.A (oa.onB.act a) (oa.onB.act (star a))) Out.rosatiε hA
  have hPM := hasGen_pullMul oa.onB.toRingAct w0 a N hN uΨ huΨ uR huR D.toPre.cub.t D.toPre.cub.isGen
  have hRig : HasGen D.toPre.P.L (lf (Finsupp.single (1 : D.toPre.P.A ⟶ D.toPre.P.A) 1)) := by
    have := HasGen.of_gen (LB.pullGen D.toPre.P.L _ _ D.toPre.rig (toUnit D.toPre.P.A).left)
      (pullGen_isGen_of_isGen _ _ D.toPre.rig D.toPre.rig_gen _)
    convert this using 1
    simp only [fsum, Fintype.univ_punit, Finset.sum_singleton, lf_single]
    rfl
  have h := (hPM.zsmul (-(k : ℤ))).add (hRig.zsmul ((k : ℤ) * ((N : ℤ) - 1)))
  simp only [← lf_smul, ← lf_add] at h
  have hf : fsum (K := Fin 2) ![𝟙 D.toPre.P.A.left, (oa.onB.act a).left] ![((k * N : ℕ) : ℤ), -(k : ℤ)] =
      lf (-(k : ℤ) • (Finsupp.single (oa.onB.act a) 1 - (N : ℤ) • Finsupp.single (𝟙 D.toPre.P.A) 1 +
        ((N : ℤ) - 1) • Finsupp.single (1 : D.toPre.P.A ⟶ D.toPre.P.A) 1) +
        ((k : ℤ) * ((N : ℤ) - 1)) • Finsupp.single (1 : D.toPre.P.A ⟶ D.toPre.P.A) 1) := by
    simp only [fsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [← Over.id_left, ← lf_single, ← lf_single, ← lf_add]
    congr 1
    rw [← Finsupp.smul_single_one, ← Finsupp.smul_single_one _ (-(k : ℤ))]
    push_cast
    module
  obtain ⟨X0, hX0⟩ := h.gen hL _ _ hf
  have hzp : eSec D.toPre.P.A ≫ (toUnit D.toPre.P.A).left = 𝟙 _ := by
    simp only [eSec, ← Over.comp_left]
    rw [show η[D.toPre.P.A] ≫ toUnit D.toPre.P.A = 𝟙 _ from toUnit_unique _ _]
    rfl
  have hrig : (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rig (k * (N - 1))).IsGen :=
    powGen_isGen_of_isGen _ D.toPre.rig_gen _
  refine exists_normalized_to hL _ _ X0 hX0 (toUnit D.toPre.P.A).left (eSec D.toPre.P.A) hzp _ _ _ hrig ?_
  have ha : eSec D.toPre.P.A ≫ (oa.onB.act a).left = eSec D.toPre.P.A := by
    haveI := oa.onB.hom a
    simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  simp only [fsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Category.comp_id,
    ha, Fintype.univ_punit, Finset.sum_singleton, ← Finsupp.single_add]
  congr 1
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hN1]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.G.DVR
