-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.anX_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:23:22.61652+00:00
-- url     : https://prove2.me/submissions/373f3f95-39f0-4247-ab57-e8317dd61f53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anX_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetSubstP_anAct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isHolFam_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isLocalHom_jetMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetOf_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_precomp


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
variable [Algebra c.F ℂ]
variable (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
  (y : FrPt Xo c ℂ) (hy : y.x = F.u i P)
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (m : ℕ) (a : 𝓞 E) :
    anX F i P hP y hy m ≫ Xo.univ.t.act.act a =
      homAt y.x (jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2)) ≫ anX F i P hP y hy m := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, anX_left, homAt, Over.homMk_left]
  have hol' := isHolFam_comp (anE F i P) (anHol F i P hP) (Xo.univ.t.act.act a).left
  have hc : ∀ z, anE F i P z ≫ (Xo.univ.t.act.act a).left = anE F i P (fun k => ty k (a : E) * z k) := fun z => by
    unfold anE
    rw [F.ex_lin i P hP a z, Over.comp_left]
  have h0 : (fun z => anE F i P z ≫ (Xo.univ.t.act.act a).left) 0 = anE F i P 0 := by
    show anE F i P 0 ≫ (Xo.univ.t.act.act a).left = anE F i P 0
    rw [hc]
    congr 1
    funext k
    simp
  have hloc : IsLocalHom ((jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2) :
      Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) := by
    unfold jetSubstP
    exact isLocalHom_jetMap _ _
  rw [jetPt_comp (anE F i P) (anHol F i P hP) (Xo.univ.t.act.act a).left _ hol' (fun z => rfl) m]
  refine (jetPt_precomp (anE F i P) (fun z => anE F i P z ≫ (Xo.univ.t.act.act a).left) (anHol F i P hP) hol' h0 m
    ((jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2) :
      Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m)
    (hχl := hloc) ?_).symm
  intro U hU f
  simp_rw [hc]
  rw [jetOf_scale m (fun k => ty k (a : E)) (contDiffAt_val (e := anE F i P) (hol := anHol F i P hP) hU f)]
  exact jetSubstP_anAct m a _
end ReciprocityTheory.ChartRestriction.G.PullbackSections
