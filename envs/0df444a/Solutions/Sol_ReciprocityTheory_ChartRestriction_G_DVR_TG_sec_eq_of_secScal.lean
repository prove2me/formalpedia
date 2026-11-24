-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.sec_eq_of_secScal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:13.943823+00:00
-- url     : https://prove2.me/submissions/5d267fcc-d04f-4f82-8536-257fe6d64069

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenDiv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenGeneric
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_map_inj_of_le_ge
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_app_fst_jF_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_app_toW
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_resTop_scal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_toW_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_toW_res


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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution (U : UnifPre I D A G) [Flat G.hom] (s σ : H0 U.LG.L 1) (sK : U.SecK 1) (r : R)
    (h1 : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) sK
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) s (pullback.fst G.hom (jK R)) 1)
    (h2 : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) sK
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) σ (pullback.fst G.hom (jK R))
      (scal (pullback.snd G.hom (jK R) ≫ jK R) r)) :
    ∀ j, σ.f j = toW G.hom _ r * s.f j := by
  intro (j : Fin 1 → U.LG.L.ι)
  have hc : LB.Coh U.LG.L (Sum.elim (fun _ : Fin 1 => pullback.fst G.hom (jK R))
      (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k)) (Sum.elim j j) := by
    intro a b _
    rcases a with a | a <;> rcases b with b | b <;> exact congrArg j (Subsingleton.elim _ _)
  have e1 := h1 j j hc
  have e2 := h2 j j hc
  have h1' : resTop (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j ⊓
      LB.wchart U.LG.L (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) j)
      (1 : Γ(pullback G.hom (jK R), ⊤)) = 1 := map_one _
  rw [h1', _root_.one_mul] at e1
  rw [← e1] at e2
  have hle : pullback.fst G.hom (jK R) ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j ≤
      LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j ⊓
        LB.wchart U.LG.L (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) j :=
    fun x hx => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k⟩
  apply app_fst_jF_injective G.hom
  apply map_inj_of_le_ge (inf_le_right.trans (wchart_comp_le _ _ j)) hle
  refine e2.trans ?_
  have e3 : (((pullback.fst G.hom (jK R)).app (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)).hom
      (toW G.hom (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) r *
        (show Γ(G.left, LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) from s.f j))) =
      toW (pullback.fst G.hom (jK R) ≫ G.hom) _ r *
        ((pullback.fst G.hom (jK R)).app (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)).hom
          (show Γ(G.left, LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) from s.f j) := by
    rw [map_mul, app_toW]
  erw [e3, map_mul, toW_res, resTop_scal, toW_congr pullback.condition.symm]
end ReciprocityTheory.ChartRestriction.G.DVR.TG
