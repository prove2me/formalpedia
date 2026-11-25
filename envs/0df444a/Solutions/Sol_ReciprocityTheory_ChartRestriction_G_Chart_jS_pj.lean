-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.jS_pj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:56:37.716773+00:00
-- url     : https://prove2.me/submissions/685d1ebd-bf51-4818-afda-86e87d125488

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ChartSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pj_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jS_zR
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.Canon
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (m : ℕ) (a : σ → MvPowerSeries τ R) (ha) (f : MvPowerSeries σ R) : jS m a ha (pj m f) = pj m (subst a f) := by
  have e : ∀ p : MvPolynomial σ R, MvPolynomial.aeval (fun s => ((truncTotal (m + 1) (a s) : MvPolynomial τ R) :
      MvPowerSeries τ R)) p = ((MvPolynomial.aeval (fun s => truncTotal (m + 1) (a s)) p : MvPolynomial τ R) :
        MvPowerSeries τ R) := fun p => by
    induction p using MvPolynomial.induction_on with
    | C r => simp [MvPowerSeries.algebraMap_apply]
    | add p q hp hq => simp [hp, hq]
    | mul_X p s hp => simp [hp]
  rw [pj.eq_def m (subst a f), truncTotal_subst ha, subst_coe, e]
  refine Eq.trans ?_ (pj_coe m _).symm
  have h : (jS m a ha).comp (Ideal.Quotient.mkₐ R _) =
      (Ideal.Quotient.mkₐ R _).comp (MvPolynomial.aeval fun s => truncTotal (m + 1) (a s)) :=
    MvPolynomial.algHom_ext fun s => (jS_zR m a ha s).trans (by rw [AlgHom.comp_apply, MvPolynomial.aeval_X]; rfl)
  exact AlgHom.congr_fun h _
end ReciprocityTheory.ChartRestriction.G.Chart
