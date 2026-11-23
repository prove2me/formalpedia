-- Prove2me | solution 1 for PI.VolStabW.iInter_thick
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:56:53.742095+00:00
-- url     : https://prove2.me/submissions/533d49e1-4b83-4778-9097-e37fcd8775ca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_CosDens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_MeasureEqOfCos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Topology Set Filter
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
omit [MeasurableSpace X] [OpensMeasurableSpace X]
namespace PI.VolStabW
theorem _root_.solution (S : Set X) (hSc : IsClosed S) (Λ : ℕ → AddSubgroup X)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N) : ⋂ n, thick S (Λ n) = S := by
  ext x
  simp only [mem_iInter]
  constructor
  · intro hx
    rw [← hSc.closure_eq, mem_closure_iff_nhds]
    intro N hN
    have h0 : {d : X | x - d ∈ N} ∈ 𝓝 (0 : X) := by
      have hc : Continuous fun d : X => x - d := continuous_const.sub continuous_id
      have := hc.continuousAt (x := 0) (by simpa using hN)
      exact this
    obtain ⟨n, hn⟩ := hb _ h0
    obtain ⟨s, hs, hxs⟩ := hx n
    have := hn hxs
    simp only [mem_setOf_eq, sub_sub_cancel] at this
    exact ⟨s, this, hs⟩
  · intro hx n
    exact ⟨x, hx, by simp [(Λ n).zero_mem]⟩
end PI.VolStabW
