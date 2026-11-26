-- Prove2me | solution 1 for Stanley.count_allSources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:11.012718+00:00
-- url     : https://prove2.me/submissions/e457873d-18e3-4ead-9c4e-cfa3ad0cf21c

module
public import Definitions.Def_Stanley_Orientation
public import Definitions.Def_Stanley_SourceSum

set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
open Classical
namespace Stanley
theorem _root_.solution (s : Finset V) :
    (Fintype.card {D : AcyclicOrientation G // D.AllSources (s : Set V)} : ℤ) =
      if Independent G (s : Set V) then orientationCount (G.induce (s : Set V)ᶜ) else 0 := by
  classical
  rw [Fintype.card_congr (AcyclicOrientation.sourceEquiv (s : Set V))]
  by_cases hs : Independent G (s : Set V) <;> simp [hs, orientationCount, Nat.card_eq_fintype_card]
end Stanley
