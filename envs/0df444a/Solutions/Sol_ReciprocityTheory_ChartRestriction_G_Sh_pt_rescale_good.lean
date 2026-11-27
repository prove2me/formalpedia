-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_rescale_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:55.005233+00:00
-- url     : https://prove2.me/submissions/5392fecd-7c90-4ca7-9544-89ba26322e65

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
theorem _root_.solution {c : C} (hc : c ∈ ptIntSub v) {ga : Fin d → PowerSeries C}
    (h : PTGood v ga) : PTGood v (rescaleCurve c ga) := by
  intro i
  obtain ⟨h0, hi⟩ := h i
  have hi' : ∀ e, coeff e (ga i) ∈ ptIntSub v := hi
  refine ⟨rc_lemma_8 c (ga i) h0, ?_⟩
  show ∀ e, coeff e (PowerSeries.rescale c (ga i)) ∈ ptIntSub v
  intro e
  obtain ⟨n, rfl⟩ : ∃ n, e = Finsupp.single () n := ⟨e (), Finsupp.unique_single e⟩
  rw [rs_lemma_6]
  exact Subring.mul_mem _ (Subring.pow_mem _ hc n) (hi' _)
end ReciprocityTheory.ChartRestriction.G.Sh
