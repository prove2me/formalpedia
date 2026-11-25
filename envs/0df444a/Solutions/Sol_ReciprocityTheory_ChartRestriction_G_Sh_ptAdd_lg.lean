-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptAdd_lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:28:56.501255+00:00
-- url     : https://prove2.me/submissions/8b47cb53-2ed1-410a-b17e-d56723553b5f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptc_elim_const
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
private theorem hs_lemma {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero ha
end
end ReciprocityTheory.ChartRestriction.G.Sh
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution (G : LogFGL v d) {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (a : Fin d) :
    subst (ptAdd G x y) (G.lg a) = subst x (G.lg a) + subst y (G.lg a) := by
  have hxy := hs_lemma (ptc_elim_const hx hy)
  have hF := hs_lemma G.F_const
  have hl : HasSubst (fun b : Fin d => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hs_lemma fun b => by simp
  have hr : HasSubst (fun b : Fin d => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hs_lemma fun b => by simp
  rw [show ptAdd G x y = fun s => subst (Sum.elim x y) (G.F s) from rfl,
    ← subst_comp_subst_apply hF hxy, G.lg_F a, subst_add hxy,
    subst_comp_subst_apply hl hxy, subst_comp_subst_apply hr hxy]
  simp only [subst_X hxy, Sum.elim_inl, Sum.elim_inr]
end ReciprocityTheory.ChartRestriction.G.Sh
