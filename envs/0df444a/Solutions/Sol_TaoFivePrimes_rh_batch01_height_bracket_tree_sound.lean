-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_bracket_tree_sound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T17:01:36.609513+00:00
-- url     : https://prove2.me/submissions/80b5b5c9-5b43-4418-9791-4dd5e9ae311c

import Definitions.Def_TaoFivePrimes_RHBatch01HeightBracketInterface
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RHBatch01HeightTreeProof
open RHBatch01HeightBracketData RHBatch01HeightBracketInterface
lemma span {l r n : Nat} (t : Tree l r n) : l<r ∧ r≤4096 := by
  induction t with
  | leaf b => exact b.bound
  | join u v h ihu ihv =>
    exact ⟨ihu.1.trans_le (h.trans ihv.1.le),ihv.2⟩
lemma bounds {l r n : Nat} (t : Tree l r n) :
    ∀ p ∈ leaves t, l≤p.l ∧ p.r≤r := by
  induction t with
  | leaf b =>
    intro p hp
    have he : p=b := by simpa [leaves] using hp
    subst p
    exact ⟨le_rfl,le_rfl⟩
  | join u v h ihu ihv =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ⟨(ihu p hp).1,(ihu p hp).2.trans (h.trans (span v).1.le)⟩
    · exact ⟨(span u).1.le.trans (h.trans (ihv p hp).1),(ihv p hp).2⟩
lemma length {l r n : Nat} (t : Tree l r n) : (leaves t).length=n := by
  induction t with
  | leaf b => rfl
  | join u v h ihu ihv => simpa only [leaves,List.length_append,ihu,ihv]
lemma pairwise {l r n : Nat} (t : Tree l r n) :
    (leaves t).Pairwise (fun p q => p.r≤q.l) := by
  induction t with
  | leaf b => simp [leaves]
  | join u v h ihu ihv =>
    rw [leaves,List.pairwise_append]
    refine ⟨ihu,ihv,?_⟩
    intro p hp q hq
    exact (bounds u p hp).2.trans (h.trans (bounds v q hq).1)
end RHBatch01HeightTreeProof

theorem solution {l r n : Nat} (t : RHBatch01HeightBracketData.Tree l r n) :
    (RHBatch01HeightBracketInterface.leaves t).length=n ∧
    (RHBatch01HeightBracketInterface.leaves t).Pairwise (fun p q => p.r≤q.l) ∧
    (∀ p ∈ RHBatch01HeightBracketInterface.leaves t, l≤p.l ∧ p.r≤r) :=
  ⟨RHBatch01HeightTreeProof.length t,RHBatch01HeightTreeProof.pairwise t,RHBatch01HeightTreeProof.bounds t⟩
#print axioms solution
