-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB.contDiffOn_param_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:19.832784+00:00
-- url     : https://prove2.me/submissions/af93c3c3-adfd-41f7-969d-fe3dd397f99a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandGB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GelfandGB_continuous_mop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GelfandGB_hasFDerivAt_param

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [ProperSpace H] [FiniteDimensional ℂ H]
  {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  [T2Space K]
  (ν : Measure K) [IsFiniteMeasure ν]
  (c : K → H →L[ℂ] H) (hc : Continuous c) {U Ω : Set H} (hU : IsOpen U) (hΩ : IsOpen Ω)
  (hUΩ : ∀ x ∈ U, ∀ k, c k x ∈ Ω)
include hc hU hΩ hUΩ
namespace ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB
theorem _root_.solution (m : ℕ) : ∀ {E' E : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] (f : H → E') (L : K → E' →L[ℂ] E),
    ContDiffOn ℂ ∞ f Ω → Continuous L → ContDiffOn ℂ m (fun x => ∫ k, L k (f (c k x)) ∂ν) U := by
  induction m with
  | zero =>
    intro E' E _ _ _ _ _ _ f L hf hL
    have hf1 : ContDiffOn ℂ 1 f Ω := hf.of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp | decide : (1 : WithTop ℕ∞) ≤ ∞)
    have h0 : ContDiffOn ℂ 0 (fun x => ∫ k, L k (f (c k x)) ∂ν) U :=
      contDiffOn_zero.mpr fun x hx =>
        (hasFDerivAt_param ν c hc hU hΩ hUΩ f L hf1 hL hx).continuousAt.continuousWithinAt
    exact_mod_cast h0
  | succ m ih =>
    intro E' E _ _ _ _ _ _ f L hf hL
    have hf1 : ContDiffOn ℂ 1 f Ω := hf.of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp | decide : (1 : WithTop ℕ∞) ≤ ∞)
    have hd := fun x (hx : x ∈ U) => hasFDerivAt_param ν c hc hU hΩ hUΩ f L hf1 hL hx
    have hf' : ContDiffOn ℂ ∞ (fderiv ℂ f) Ω := ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).mp hf).2
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    exact (ih (fderiv ℂ f) (fun k => Mop c L k) hf' (continuous_mop c hc hL)).congr
      fun x hx => (hd x hx).fderiv
end ReciprocityTheory.ChartRestriction.DS.S7.GelfandGB
