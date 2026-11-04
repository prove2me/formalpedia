-- Prove2me | solution 1 for ThreeSum.TernaryCoverTupleCount.tuple_split_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:52:58.291651+00:00
-- url     : https://prove2.me/submissions/7ebea338-6a6c-4c63-b85b-7728c4c0259a

import Definitions.Def_Submission_ThreeSum_TernaryCoverPairStep
import Mathlib.Data.Fin.Tuple.Basic
import Definitions.Def_Submission_ThreeSum_TernaryCoverTupleCount

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverTupleCount
open Finset TernaryCoverRankFibers TernaryCoverPairStep
variable {K E ι : Type*} [Field K] [Fintype E] [Fintype ι] [DecidableEq K]
namespace ThreeSum.TernaryCoverTupleCount
theorem _root_.solution (left right : E → ι → K) (n : ℕ)
    (S : Submodule K (Fin (n+1) → K × K)) :
    (tupleSet left right (n+1) S).card =
      (pairedSet left right (tupleColumn left right)
        (S.map (splitRows (K := K) n).toLinearMap)).card := by
  classical
  apply card_bij (fun es _ => (Fin.tail es, es 0))
  · intro es hes
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro i
    exact ⟨tupleColumn left right es i, (mem_filter.mp hes).2 i, rfl⟩
  · intro es _ fs _ he
    have ht := congrArg Prod.fst he
    have hh := congrArg Prod.snd he
    change Fin.tail es = Fin.tail fs at ht
    change es 0 = fs 0 at hh
    rw [← Fin.cons_self_tail es, ← Fin.cons_self_tail fs, ht, hh]
  · intro ze hze
    refine ⟨Fin.cons ze.2 ze.1, ?_, ?_⟩
    · apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      intro i
      obtain ⟨v, hv, he⟩ := (mem_filter.mp hze).2 i
      have heq : v = tupleColumn left right (Fin.cons ze.2 ze.1) i := by
        apply (splitRows (K := K) n).injective
        change (Fin.tail v, v 0) = (tupleColumn left right ze.1 i,
          (left ze.2 i, right ze.2 i)) at he
        exact he
      exact heq ▸ hv
    · simp
end ThreeSum.TernaryCoverTupleCount
