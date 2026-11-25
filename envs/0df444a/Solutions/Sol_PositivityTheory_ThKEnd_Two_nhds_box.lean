-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.nhds_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:59:53.879621+00:00
-- url     : https://prove2.me/submissions/86f5a7db-7ef6-4bc7-996b-707abb04dcbd

import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ClosedEmb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter Matrix NumberField IsDedekindDomain
open scoped Pointwise MatrixGroups
variable {R : Type} [CommRing R]
variable [TopologicalSpace R] [IsTopologicalRing R]
namespace PositivityTheory.ThKEnd.Two
theorem _root_.solution {W : Set SL(2, R)} (hW : W ∈ 𝓝 1) : ∃ O ∈ 𝓝 (0 : R), ∀ y : SL(2, R), (∀ i j, (y.1 - 1) i j ∈ O) → y ∈ W := by
  obtain ⟨O₁, h1, h2⟩ := (mem_nhds_subtype _ _ _).1 hW
  have h3 : (fun M : Fin 2 → Fin 2 → R => Matrix.of M + 1) ⁻¹' O₁ ∈ 𝓝 0 :=
    ((show Continuous (Matrix.of : (Fin 2 → Fin 2 → R) → _) from continuous_id).add continuous_const).continuousAt.preimage_mem_nhds
      (by change O₁ ∈ 𝓝 ((0 : Matrix (Fin 2) (Fin 2) R) + 1); rw [zero_add]; exact h1)
  rw [nhds_pi, Filter.mem_pi] at h3
  obtain ⟨I, -, t, h4, h5⟩ := h3
  simp only [nhds_pi, Filter.mem_pi] at h4
  choose J _ s h6 h7 using h4
  refine ⟨⋂ i, ⋂ j, s i j, by simpa using h6, fun y hy => h2 ?_⟩
  have := h5 (a := fun i j => (y.1 - 1) i j) fun i _ => h7 i fun j _ => Set.mem_iInter₂.1 (hy i j) i j
  change Matrix.of (fun i j => (y.1 - 1) i j) + 1 ∈ O₁ at this
  rwa [show Matrix.of (fun i j => (y.1 - 1) i j) = y.1 - 1 from rfl, sub_add_cancel] at this
end PositivityTheory.ThKEnd.Two
