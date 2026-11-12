-- Prove2me | solution 1 for QEC.Coding.BDL26RXDifferentialMasks.first_step_hull_forces_other_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:48:49.986851+00:00
-- url     : https://prove2.me/submissions/25e17b76-4538-4b09-99ca-d367e7dafb6f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_subset_incidenceHull
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_saturated

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
open BDL26FiniteAlternatingCore
namespace QEC.Coding.BDL26RXDifferentialMasks
theorem _root_.solution (S : OddScale) (depth : Nat) (hd : 0 < depth) :
    (4 : BaseQubit) ∈ incidenceHull S depth ⟨0,hd⟩ {(0 : BaseQubit)} ∧
      incidenceHull S depth ⟨0,hd⟩ {(0 : BaseQubit)} ≠ {(0 : BaseQubit)} := by
  have h0 : (0 : BaseQubit) ∈ incidenceHull S depth ⟨0,hd⟩ {(0 : BaseQubit)} :=
    subset_incidenceHull S depth ⟨0,hd⟩ _ (Finset.mem_singleton_self (0 : BaseQubit))
  have h4 : (4 : BaseQubit) ∈ incidenceHull S depth ⟨0,hd⟩ {(0 : BaseQubit)} := by
    apply incidenceHull_saturated S depth ⟨0,hd⟩ _ (0 : BaseQubit) h0 (4 : BaseQubit) (0 : BaseZ)
    · change baseTannerSquarePresentation.qz (0 : BaseQubit) (0 : BaseZ) = true
      decide
    · change baseTannerSquarePresentation.qz (4 : BaseQubit) (0 : BaseZ) = true
      decide
  refine ⟨h4, ?_⟩
  intro he
  rw [he] at h4
  have hnot : (4 : BaseQubit) ∉ ({(0 : BaseQubit)} : Finset BaseQubit) := by decide
  exact hnot h4
end QEC.Coding.BDL26RXDifferentialMasks
