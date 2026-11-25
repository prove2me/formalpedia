-- Prove2me | solution 1 for SinkReset.Plan.wins_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:18.925535+00:00
-- url     : https://prove2.me/submissions/1f11eea5-de5e-4c70-b0dd-c3ba87277c35

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
variable {n : ℕ} [NeZero n] (A : Automaton n)
namespace SinkReset.Plan
theorem _root_.solution {k : ℕ} {S T : Finset (Fin n)}
    (h : A.AliceWins k T) (hST : S ⊆ T) : A.AliceWins k S := by
  induction h generalizing S with
  | reset T hT => exact .reset S fun q hq => hT q (hST hq)
  | step T a ha _ ih =>
    exact .step S a ha fun u hu hlen => ih u hu hlen (Finset.image_subset_image hST)
end SinkReset.Plan
