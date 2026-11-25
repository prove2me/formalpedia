-- Prove2me | solution 1 for PI.OmFibreUniq.W.open_eq_countable_union
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:05:45.409002+00:00
-- url     : https://prove2.me/submissions/8af71e6a-9bad-43e6-b924-081cddd5dc1b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_UniqGen
import Theorems.Thm_PI_OmFibreUniq_W_exists_compact_open

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
variable [SecondCountableTopology V]
namespace PI.OmFibreUniq.W
theorem _root_.solution {W : Set V} (hW : IsOpen W) :
    ∃ T : Set (Set V), T.Countable ∧ (∀ K ∈ T, IsCompact K ∧ IsOpen K ∧ K ⊆ W) ∧ ⋃₀ T = W := by
  choose K hK using fun x : W => exists_compact_open hW x.2
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable K (fun x => (hK x).2.1)
  refine ⟨K '' T, hTc.image K, ?_, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact ⟨(hK x).1, (hK x).2.1, (hK x).2.2.2⟩
  · rw [sUnion_image, hTU]
    ext y
    simp only [mem_iUnion]
    constructor
    · rintro ⟨x, hy⟩
      exact (hK x).2.2.2 hy
    · intro hy
      exact ⟨⟨y, hy⟩, (hK ⟨y, hy⟩).2.2.1⟩
end PI.OmFibreUniq.W
