-- Prove2me | solution 1 for ULHC.TF.pred_ne_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:54.768975+00:00
-- url     : https://prove2.me/submissions/7c3cad1b-5caf-4683-998f-80bb60448bfe

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
import Theorems.Thm_ULHC_TF_mem_inc4
import Theorems.Thm_ULHC_TF_other_other
import Theorems.Thm_ULHC_TF_other_black
import Theorems.Thm_ULHC_TF_mem_nbr
import Theorems.Thm_ULHC_TF_mem_layer_succ
import Theorems.Thm_ULHC_other_inc


set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF
namespace ULHC.TF
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {k : ℕ} {v : Pt}
    (hv : v ∈ layer V F (k + 1)) (hvk : v ∉ layer V F k) : pred V F (layer V F k) v ≠ none := by
  rcases mem_layer_succ.1 hv with h | ⟨u, hu, huv⟩
  · exact absurd h hvk
  obtain ⟨e, heu, ⟨hE, hb, hw⟩, rfl⟩ := mem_nbr.1 huv
  have hev : e.p = other e u ∨ e.q = other e u := other_inc
  intro hn
  unfold pred at hn
  have := List.find?_eq_none.1 hn e (mem_inc4.2 hev)
  apply this
  rw [decide_eq_true_iff]
  have hc := other_black heu
  refine ⟨hE, by rw [other_other heu]; exact hu, fun h => ?_, fun h => ?_⟩
  · by_contra h'; exact (hc.1 h) (by_contra fun h'' => h' (hw h''))
  · exact hb (by by_contra h''; exact h (hc.2 h''))
end ULHC.TF
