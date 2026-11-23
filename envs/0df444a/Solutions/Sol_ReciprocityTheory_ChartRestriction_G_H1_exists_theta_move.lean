-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.exists_theta_move
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:47.706409+00:00
-- url     : https://prove2.me/submissions/b789cea4-b2fc-436a-8522-25547595b74d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_tr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_exists_gen_move


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
variable {L₀ : LB G.left} {L₁ : LB A.left}
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) (k : ℤ)
    (x : T ⟶ A) (θ₀ : ThetaGrp G L₀ k T₀) (hx : τ ≫ θ₀.pt.left = x.left ≫ φ) :
    ∃ θ : ThetaGrp A L₁ k T, θ.pt = x ∧
      PMaps w ![(snd T A).left, (translPt A θ.pt).left] ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![k, -k]
        θ.φ θ₀.φ (psiO hp τ hτ).left := by
  obtain ⟨a, ha, hm⟩ := exists_gen_move hL₀ hL₁ w ((isGen_iff w).1 hw)
    ![(snd T₀ G).left, (translPt G θ₀.pt).left] ![(snd T A).left, (translPt A x).left] ![k, -k]
    (psiO hp τ hτ).left (fun i => by
      fin_cases i
      · exact (psi_snd hp τ hτ).symm
      · exact (psi_tr hp τ hτ x θ₀.pt hx).symm) θ₀.φ θ₀.isGen
  exact ⟨⟨x, a, ha⟩, rfl, hm⟩
end ReciprocityTheory.ChartRestriction.G.H1
