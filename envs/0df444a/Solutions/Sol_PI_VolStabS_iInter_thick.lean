-- Prove2me | solution 1 for PI.VolStabS.iInter_thick
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:52.518294+00:00
-- url     : https://prove2.me/submissions/fec63575-bfab-451b-8eea-335338f20522

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_CosDens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_MeasureEqOfCos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open MeasureTheory Topology Set Filter
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
omit [MeasurableSpace X] [OpensMeasurableSpace X]
namespace PI.VolStabS
theorem _root_.solution (S : Set X) (hSc : IsClosed S) (Λ : ℕ → AddSubgroup X)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N) : ⋂ n, thick S (Λ n) = S := by
  ext x
  simp only [mem_iInter]
  constructor
  · intro hx
    by_contra hxS
    have hN : (fun u => x - u) ⁻¹' Sᶜ ∈ 𝓝 (0 : X) := by
      apply (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
      simpa using hSc.isOpen_compl.mem_nhds hxS
    obtain ⟨n, hn⟩ := hb _ hN
    obtain ⟨s, hs, hxs⟩ := hx n
    have hmem := hn hxs
    simp only [mem_preimage, mem_compl_iff, sub_sub_cancel] at hmem
    exact hmem hs
  · intro hx n
    exact ⟨x, hx, by simp⟩
end PI.VolStabS
