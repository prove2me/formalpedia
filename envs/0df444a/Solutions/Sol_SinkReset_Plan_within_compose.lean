-- Prove2me | solution 1 for SinkReset.Plan.within_compose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:49:58.687295+00:00
-- url     : https://prove2.me/submissions/340a0eac-0528-4f9a-91cf-aab32b3544b9

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_act_append
public import Theorems.Thm_SinkReset_Plan_word_append

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)
namespace SinkReset.Plan
theorem _root_.solution (S : Finset (Fin n)) (u : List (Letter n))
    (hu : A.IsWord u) (b : ℕ) (h : Within A (S.image (act u)) b) :
    Within A S (u.length + b) := by
  obtain ⟨v, ⟨hv, hv0⟩, hlen⟩ := h
  refine ⟨u ++ v, ⟨(word_append A u v).2 ⟨hu, hv⟩, fun q hq => ?_⟩, ?_⟩
  · rw [act_append]; exact hv0 _ (Finset.mem_image_of_mem _ hq)
  · rw [List.length_append]; omega
end SinkReset.Plan
