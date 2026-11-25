-- Prove2me | solution 1 for PI.VolStabW.DeterminantAdmissible.boxes_seq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:27:14.341536+00:00
-- url     : https://prove2.me/submissions/88b58c7a-a7d1-42fd-8729-6df85b071b62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_isOpen_boxS
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_exists_box_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DeterminantAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
namespace PI.VolStabW.DeterminantAdmissible
theorem _root_.solution : ∃ bs : ℕ → Set (ι → Af F), (∀ n, bs n ∈ boxes F ι) ∧ ⋃ n, bs n = univ := by
  obtain ⟨T, hT, he⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun s : {s // s ∈ boxes F ι} => (s.1 : Set (ι → Af F)))
    (fun s => by obtain ⟨D, hD, e⟩ := s.2; rw [e]; exact isOpen_boxS hD)
  have hU : ⋃ s ∈ T, (s.1 : Set (ι → Af F)) = univ := by
    rw [he]
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨D, hD, hy⟩ := exists_box_mem y
    exact mem_iUnion.2 ⟨⟨boxS D, D, hD, rfl⟩, hy⟩
  have hne : T.Nonempty := by
    have h0 : (0 : ι → Af F) ∈ ⋃ s ∈ T, (s.1 : Set (ι → Af F)) := by
      rw [hU]
      trivial
    obtain ⟨s, hs, -⟩ := mem_iUnion₂.1 h0
    exact ⟨s, hs⟩
  obtain ⟨g, hg⟩ := hT.exists_eq_range hne
  refine ⟨fun n => (g n).1, fun n => (g n).2, ?_⟩
  rw [← hU, hg]
  ext y
  simp
end PI.VolStabW.DeterminantAdmissible
