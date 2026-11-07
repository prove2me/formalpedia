-- Prove2me | solution 1 for QEC.Locality.ConnectedSetCounting.rooted_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:47:32.756846+00:00
-- url     : https://prove2.me/submissions/d4ac9a3b-5613-4402-a3de-efbe46ffe509

import Definitions.Def_QEC_Locality_Graph_Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_induced_set_trace
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_traces_card_le
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_mem_rooted

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.ConnectedSetCounting
theorem _root_.solution (G : SimpleGraph V) (Delta : Nat)
    (hd : ∀ r, Nat.card {w : V // G.Adj r w} ≤ Delta) (r : V) (m : Nat) :
    (rooted G r m).card ≤ (Delta+1)^(2*m) := by
  classical
  have hsub : rooted G r m ⊆ (traces G r (2*m)).image List.toFinset := by
    intro A hA
    obtain ⟨hr,hm,hc⟩ := (mem_rooted G r m A).mp hA
    obtain ⟨l,hl,hs⟩ := induced_set_trace G A r hr hc
    exact Finset.mem_image.mpr ⟨l,hm ▸ hl,hs⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (traces_card_le G Delta hd r (2*m)))
end QEC.Locality.ConnectedSetCounting
