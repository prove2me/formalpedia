-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_expS_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:57:28.071474+00:00
-- url     : https://prove2.me/submissions/c168a44c-0344-42bd-a8ce-e5c0cb3dd780

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_subst_add_two_vars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
section Exp2
variable (A : Type) [CommRing A] [Algebra ℚ A]
end Exp2
section Ev
variable {k : Type} [CommRing k] {d : ℕ}
private theorem gt_substExp_lemma [Algebra ℚ k] {τ : Type} {b : Fin 2 → MvPowerSeries τ k}
    (hb : MvPowerSeries.HasSubst b) (p : MvPowerSeries (Fin 2) k) (hp : constantCoeff p = 0) :
    MvPowerSeries.subst b (PowerSeries.subst p (PowerSeries.exp k)) =
      PowerSeries.subst (MvPowerSeries.subst b p) (PowerSeries.exp k) :=
  MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ : Unit => hp)) hb _
end Ev
section Calc
variable {k : Type} [CommRing k] {d : ℕ}
end Calc
section Calc2
variable {k : Type} [CommRing k] {d : ℕ}
end Calc2
section Main
end Main
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution [Algebra ℚ k] {n : ℕ} (f g : PS k n d) (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : FB.expS k (f + g) = FB.expS k f * FB.expS k g := by
  have hb : MvPowerSeries.HasSubst (![f, g] : Fin 2 → PS k n d) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun j => by fin_cases j <;> simp [hf, hg])
  have key := congrArg (MvPowerSeries.subst (![f, g] : Fin 2 → PS k n d)) (exp_subst_add_two_vars k)
  have e1 := gt_substExp_lemma hb ((X 0 : MvPowerSeries (Fin 2) k) + X 1) (by simp)
  have e2 := gt_substExp_lemma hb (X 0 : MvPowerSeries (Fin 2) k) (by simp)
  have e3 := gt_substExp_lemma hb (X 1 : MvPowerSeries (Fin 2) k) (by simp)
  rw [MvPowerSeries.subst_mul hb, e1, e2, e3, MvPowerSeries.subst_add hb,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb] at key
  simpa [FB.expS] using key
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
