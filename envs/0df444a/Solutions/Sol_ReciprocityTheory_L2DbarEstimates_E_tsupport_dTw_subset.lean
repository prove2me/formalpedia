-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.tsupport_dTw_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:35.992537+00:00
-- url     : https://prove2.me/submissions/e3cc9451-5229-4d50-988d-f600a461a693

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate ContDiff
noncomputable section
private theorem d_eq_zero_of_eventuallyEq_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (u : M → ℂ) (x : M) (hu : u =ᶠ[nhds x] 0) : d n z j u x = 0 := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · rw [d, dif_pos h]
    obtain ⟨he, hx⟩ := Classical.choose_spec h
    set e := Classical.choose h
    have hzx : z x = e x := he hx
    have hc : ContinuousAt e.symm (z x) := by
      rw [hzx]
      exact e.continuousAt_symm (e.map_source hx)
    have hx0 : e.symm (z x) = x := by
      rw [hzx]
      exact e.left_inv hx
    have hev : u ∘ e.symm =ᶠ[nhds (z x)] fun _ => (0 : ℂ) := by
      have ht := hc.tendsto
      rw [hx0] at ht
      exact ht.eventually hu
    simp only [wd, hev.fderiv_eq]
    simp
  · rw [d, dif_neg h]
end
end ReciprocityTheory.L2DbarEstimates.E
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.E
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (j : Fin n) (u : M → ℂ) :
    tsupport (dTw n z ph j u) ⊆ tsupport u := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport u)
  by_contra hxu
  apply hx
  have hu0 : u =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 hxu
  simp only [dTw]
  rw [d_eq_zero_of_eventuallyEq_zero n z j u x hu0, hu0.eq_of_nhds]
  simp
end ReciprocityTheory.L2DbarEstimates.E
