-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.hasDerivAt_tensL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:50.817472+00:00
-- url     : https://prove2.me/submissions/929204b6-f8c3-42b4-93f3-fcd5ec4e7d62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {m : ℝ → Matrix ι ι ℂ} {m' : Matrix ι ι ℂ} {S : ℝ → V →L[ℂ] V}
    {S' : V →L[ℂ] V} {t₀ : ℝ} (hm : ∀ i j, HasDerivAt (fun t => m t i j) (m' i j) t₀)
    (hS : HasDerivAt S S' t₀) :
    HasDerivAt (fun t => tensL (m t) (S t)) (tensL m' (S t₀) + tensL (m t₀) S') t₀ := by
  have h : ∀ i j, HasDerivAt
      (fun t => m t i j • (piIn i ∘L S t ∘L PiLp.proj 2 (fun _ : ι => V) j))
      (m t₀ i j • (piIn i ∘L S' ∘L PiLp.proj 2 (fun _ : ι => V) j) +
        m' i j • (piIn i ∘L S t₀ ∘L PiLp.proj 2 (fun _ : ι => V) j)) t₀ := by
    intro i j
    let L : (V →L[ℂ] V) →L[ℂ] (PiLp 2 (fun _ : ι => V) →L[ℂ] PiLp 2 (fun _ : ι => V)) :=
      (ContinuousLinearMap.compL ℂ (PiLp 2 (fun _ : ι => V)) V (PiLp 2 (fun _ : ι => V)) (piIn i)).comp
        ((ContinuousLinearMap.compL ℂ (PiLp 2 (fun _ : ι => V)) V V).flip
          (PiLp.proj 2 (fun _ : ι => V) j))
    have hc : HasDerivAt (fun t => L (S t)) (L S') t₀ :=
      (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t₀ hS
    exact (hm i j).smul hc
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ => h i j
  refine hs.congr_deriv ?_
  simp only [tensL, Finset.sum_add_distrib]
  exact add_comm _ _
end ReciprocityTheory.ChartRestriction.DS.HW
