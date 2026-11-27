-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_lg_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:48.758293+00:00
-- url     : https://prove2.me/submissions/ea68b74e-d70d-4ce7-9b8f-a436296a3e02

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
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
private theorem rs_lemma_6 (c : C) (f : PowerSeries C) (n : ℕ) :
    coeff (Finsupp.single () n) (PowerSeries.rescale c f) =
      c ^ n * coeff (Finsupp.single () n) f :=
  PowerSeries.coeff_rescale f c n
private theorem rc_lemma_8 (c : C) (f : PowerSeries C) (hf : constantCoeff f = 0) :
    constantCoeff (PowerSeries.rescale c f) = 0 := by
  have h1 := rs_lemma_6 c f 0
  rw [Finsupp.single_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, mul_zero] at h1
  exact h1
private theorem rp_lemma_7 (c : C) (ga : Fin d → PowerSeries C) (m : Fin d →₀ ℕ) :
    (m.prod fun b k => (rescaleCurve c ga b) ^ k) =
      PowerSeries.rescale c (m.prod fun b k => ga b ^ k) := by
  unfold Finsupp.prod
  rw [map_prod]
  simp only [map_pow]
  rfl
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
theorem _root_.solution (G : LogFGL v d) (c : C) {ga : Fin d → PowerSeries C}
    (h0 : ∀ b, constantCoeff (ga b) = 0) (a : Fin d) :
    G.lgCurve (rescaleCurve c ga) a = PowerSeries.rescale c (G.lgCurve ga a) := by
  have hs : HasSubst ga := hs_lemma h0
  have hs' : HasSubst (rescaleCurve c ga) := hs_lemma fun b => rc_lemma_8 c (ga b) (h0 b)
  refine MvPowerSeries.ext fun e => ?_
  obtain ⟨n, rfl⟩ : ∃ n, e = Finsupp.single () n := ⟨e (), Finsupp.unique_single e⟩
  rw [rs_lemma_6, show G.lgCurve (rescaleCurve c ga) a = subst (rescaleCurve c ga) (G.lg a) from rfl,
    show G.lgCurve ga a = subst ga (G.lg a) from rfl, coeff_subst hs', coeff_subst hs,
    mul_finsum]
  apply finsum_congr
  intro m
  rw [rp_lemma_7, rs_lemma_6, smul_eq_mul, smul_eq_mul]
  ring
end ReciprocityTheory.ChartRestriction.G.Sh
