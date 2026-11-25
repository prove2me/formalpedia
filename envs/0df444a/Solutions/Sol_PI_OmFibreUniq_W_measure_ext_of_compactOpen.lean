-- Prove2me | solution 1 for PI.OmFibreUniq.W.measure_ext_of_compactOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:17:59.894868+00:00
-- url     : https://prove2.me/submissions/7b8a2a88-2897-4999-bf29-340f69cc7362

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_UniqGen
import Theorems.Thm_PI_OmFibreUniq_W_open_eq_countable_union

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
variable [MeasurableSpace V] [BorelSpace V]
namespace PI.OmFibreUniq.W
theorem _root_.solution {U : Set V} (hU : IsOpen U) (m m' : Measure V)
    (h0 : m Uᶜ = 0) (h0' : m' Uᶜ = 0)
    (hK : ∀ K, IsCompact K → IsOpen K → K ⊆ U → m K < ∞ ∧ m K = m' K) : m = m' := by
  have key : ∀ O, IsOpen O → O ⊆ U → m O = m' O := by
    intro O hO hOU
    obtain ⟨T, hTc, hT, hTO⟩ := open_eq_countable_union hO
    rcases T.eq_empty_or_nonempty with he | hne
    · rw [← hTO, he, sUnion_empty, measure_empty, measure_empty]
    obtain ⟨g, rfl⟩ := hTc.exists_eq_range hne
    have hacc : ∀ n, IsCompact (accumulate g n) ∧ IsOpen (accumulate g n) ∧ accumulate g n ⊆ U := by
      intro n
      have hg : ∀ k, IsCompact (g k) ∧ IsOpen (g k) ∧ g k ⊆ O := fun k => hT _ ⟨k, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [accumulate_def]
        exact (finite_le_nat n).isCompact_biUnion fun k _ => (hg k).1
      · rw [accumulate_def]
        exact isOpen_biUnion fun k _ => (hg k).2.1
      · rw [accumulate_def]
        exact iUnion₂_subset fun k _ => (hg k).2.2.trans hOU
    rw [← hTO, sUnion_range, measure_iUnion_eq_iSup_accumulate, measure_iUnion_eq_iSup_accumulate]
    congr 1
    funext n
    exact (hK _ (hacc n).1 (hacc n).2.1 (hacc n).2.2).2
  have hres : m.restrict U = m'.restrict U := by
    obtain ⟨T, hTc, hT, hTU⟩ := open_eq_countable_union hU
    rw [← hTU]
    refine (Measure.restrict_sUnion_congr hTc).2 fun K hKT => ?_
    obtain ⟨hKc, hKo, hKU⟩ := hT K hKT
    obtain ⟨hfin, heq⟩ := hK K hKc hKo hKU
    haveI : IsFiniteMeasure (m.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
    refine ext_of_generate_finite {s | IsOpen s} BorelSpace.measurable_eq isPiSystem_isOpen ?_ ?_
    · intro O hO
      rw [Measure.restrict_apply hO.measurableSet, Measure.restrict_apply hO.measurableSet]
      exact key _ (hO.inter hKo) (inter_subset_right.trans hKU)
    · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ, heq]
  calc m = m.restrict U := (Measure.restrict_eq_self_of_ae_mem (ae_iff.2 h0)).symm
    _ = m'.restrict U := hres
    _ = m' := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 h0')
end PI.OmFibreUniq.W
