-- Prove2me | solution 1 for WilliamsonShmoys.finite_extension_reaches_connected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T11:18:14.375643+00:00
-- url     : https://prove2.me/submissions/0ad7a370-ed1d-4b47-b417-ab205f57cae6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
namespace WilliamsonShmoys
theorem _root_.solution
    {V : Type} [Fintype V] [DecidableEq V]
    (W : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P W)
    (hstep : ∀ G : SimpleGraph V, W ≤ G → P G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G < H ∧ P H) :
    ∃ K : SimpleGraph V, W ≤ K ∧ K.Connected ∧ P K := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => W ≤ G ∧ P G)).exists_max_image
    (fun G => G.edgeFinset.card) ⟨W, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hP⟩⟩
  obtain ⟨hTQ, hQ⟩ : W ≤ Q ∧ P Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hTQ, ?_, hQ⟩
  by_contra hc
  obtain ⟨R, hlt, hR⟩ := hstep Q hTQ hQ hc
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTQ.trans hlt.le, hR⟩)
  omega
end WilliamsonShmoys

