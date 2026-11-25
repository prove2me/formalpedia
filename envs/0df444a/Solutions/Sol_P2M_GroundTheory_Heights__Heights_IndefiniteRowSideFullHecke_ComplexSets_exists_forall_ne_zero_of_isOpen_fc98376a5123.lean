-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_forall_ne_zero_of_isOpen_fc98376a5123
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:32:31.754778+00:00
-- url     : https://prove2.me/submissions/b8737cff-62c1-4f18-8ef9-b8723fab27a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProperOpenProjectionLocalUnbranched
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompactHolomorphicFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreLocalUnbranched
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperOpenProjectionLocalUnbranched

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Metric Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {E ι : Type} [TopologicalSpace E] (s : Finset ι)
    (G : ι → E → ℂ) (U : Set E) (hc : ∀ i ∈ s, ContinuousOn (G i) U)
    (hne : ∀ i ∈ s, ∀ W : Set E, IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, G i t ≠ 0) :
    ∀ W : Set E, IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, ∀ i ∈ s, G i t ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rintro W - - ⟨t, ht⟩
    exact ⟨t, ht, by simp⟩
  | insert a s ha ih =>
    intro W hWo hWU hW
    obtain ⟨t₀, ht₀W, ht₀⟩ := hne a (Finset.mem_insert_self a s) W hWo hWU hW
    have hW'o : IsOpen (W ∩ G a ⁻¹' {0}ᶜ) :=
      ((hc a (Finset.mem_insert_self a s)).mono hWU).isOpen_inter_preimage hWo isOpen_compl_singleton
    obtain ⟨t, ⟨htW, hta⟩, hts⟩ := ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
      (fun i hi => hne i (Finset.mem_insert_of_mem hi)) _ hW'o (Set.inter_subset_left.trans hWU)
      ⟨t₀, ht₀W, ht₀⟩
    refine ⟨t, htW, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hta
    · exact hts i hi
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
