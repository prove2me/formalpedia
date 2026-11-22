-- Prove2me | solution 1 for Parikh.familyWitness_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:52:03.998143+00:00
-- url     : https://prove2.me/submissions/ae2bb925-1713-4431-b1eb-d3f3a76e084d

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Definitions.Def_LeanPool_Parikh_GrammarImage
public import Definitions.Def_LeanPool_Parikh_FiniteWitness

set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*} [DecidableEq T]
namespace Parikh
theorem _root_.solution (g : ContextFreeGrammar T)
    (bases cycles : Finset (ParseTree T g.NT)) :
    (familyWitness g bases cycles).length ≤ bases.card * 2 ^ cycles.card := by
  classical
  simpa only [familyWitness, List.length_map, Finset.length_toList,
    Finset.card_product, Finset.card_powerset] using
    Finset.card_filter_le (bases ×ˢ cycles.powerset)
      (fun pair => ContextsActivatable g pair.1 pair.2)
end Parikh
