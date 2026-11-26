-- Prove2me | solution 1 for Stanley.AcyclicOrientation.exists_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:08.625015+00:00
-- url     : https://prove2.me/submissions/b309cce7-f84e-4ffd-b18a-db5adf8fea5c

module
public import Definitions.Def_Stanley_Definitions
public import Mathlib.Order.WellFounded
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_Stanley_Orientation

set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset
universe u
variable {V : Type u} (G : SimpleGraph V)
open Stanley.AcyclicOrientation
variable {G}
namespace Stanley.AcyclicOrientation
theorem _root_.solution [Nonempty V] (D : AcyclicOrientation G) : ∃ v, D.Source v := by
  obtain ⟨v, _, hv⟩ := D.wf.has_min Set.univ Set.univ_nonempty
  exact ⟨v, fun u => hv u (Set.mem_univ u)⟩
end Stanley.AcyclicOrientation
