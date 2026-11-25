-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:58:57.297797+00:00
-- url     : https://prove2.me/submissions/c1ecaf36-758f-4c28-9fd6-3e8dc7b64994

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_OrbitMapConjSmulZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_Imports
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_Canon_canonGen_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_Canon_canonGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_hsub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_linComb_cover
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ratio_glue
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_sameSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_mulGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_pullGen


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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))
include hO
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
theorem _root_.solution (hu : u.IsGen) : ∃ ρ : Γ((thickObj R I e G).left, ⊤)ˣ,
    ∀ (jA : Fin 4 ⊕ Fin 6 → D.toPre.P.L.ι) (jB : Fin 4 → D.toPre.P.L.ι),
      LB.Coh D.toPre.P.L (φA U ιD e a χ) jA → LB.Coh D.toPre.P.L (φB U ιG e a χ) jB →
      (∀ k k', φB U ιG e a χ k = φA U ιD e a χ k' → jB k = jA k') →
      res (inf_le_right : LB.wchart D.toPre.P.L (φB U ιG e a χ) jB ⊓
          LB.wchart D.toPre.P.L (φA U ιD e a χ) jA ≤ LB.wchart D.toPre.P.L (φA U ιD e a χ) jA)
          ((lhs U ιD e a χ u).s jA) =
        res le_top ρ * res inf_le_left ((rhs U ιG e a χ).s jB) := by
  have hL := D.toPre.P.isLB
  have hgA : (lhs U ιD e a χ u).IsGen :=
    LB.isGen_mulGen (L := D.toPre.P.L) _ _ _ _ _ _ ((U.gt e).t_gen _)
      (LB.isGen_pullGen (L := D.toPre.P.L) _ _ _ hu _)
  have hgB : (rhs U ιG e a χ).IsGen :=
    LB.isGen_pullGen (L := D.toPre.P.L) _ _ _ ((U.gt e).t_gen χ) _
  have hB' := Canon.canonGen_isGen hL (φB U ιG e a χ) Oinvε (φA U ιD e a χ) εA
    (sameSum U ιD ιG e a χ hO) (hsub U ιD ιG e a χ hO) (rhs U ιG e a χ) hgB
  obtain ⟨ρ, hρ⟩ := ratio_glue _ (linComb_cover _ hL _ _) _ _ hgA hB'
  refine ⟨ρ, fun jA jB cA cB cAB => ?_⟩
  have hc := Canon.canonGen_corr hL (φB U ιG e a χ) Oinvε (φA U ιD e a χ) εA
    (hsub U ιD ιG e a χ hO) (rhs U ιG e a χ) jB jA cB cA cAB
  exact (congrArg (res _) (hρ jA)).trans ((map_mul (res _) _ _).trans
    (congrArg₂ (· * ·) (Canon.res_res' _ _ _) hc.symm))
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
