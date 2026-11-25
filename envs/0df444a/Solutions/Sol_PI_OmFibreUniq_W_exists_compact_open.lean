-- Prove2me | solution 1 for PI.OmFibreUniq.W.exists_compact_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:00:37.017904+00:00
-- url     : https://prove2.me/submissions/d1c521b7-e8cf-4d28-966a-064a8620de79

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_UniqGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W
open MeasureTheory Topology Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal
variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [TotallyDisconnectedSpace V]
namespace PI.OmFibreUniq.W
theorem _root_.solution {W : Set V} (hW : IsOpen W) {x : V} (hx : x ∈ W) :
    ∃ K, IsCompact K ∧ IsOpen K ∧ x ∈ K ∧ K ⊆ W := by
  obtain ⟨s, hs, hsW, hsc⟩ := local_compact_nhds (hW.mem_nhds hx)
  obtain ⟨K, hKmem, hxK, hKsub⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (H := V)).exists_subset_of_mem_open
    (mem_interior_iff_mem_nhds.2 hs) isOpen_interior
  have hKc : IsClopen K := hKmem
  exact ⟨K, hsc.of_isClosed_subset hKc.1 (hKsub.trans interior_subset), hKc.2, hxK,
    hKsub.trans (interior_subset.trans hsW)⟩
end PI.OmFibreUniq.W
