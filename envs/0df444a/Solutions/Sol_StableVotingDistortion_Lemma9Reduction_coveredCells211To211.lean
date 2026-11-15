-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells211To211
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:45:46.758941+00:00
-- url     : https://prove2.me/submissions/417ddd89-2555-4f19-bff9-8bc347bf100b

import Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_rectWitnessSound
namespace StableVotingDistortion.PaperBox
theorem verify_split_boxes {d : ℕ} {f : Box d → Bool} (j : Fin d) (cut : ℚ)
    (l r : Cover d) (parent left right : Box d)
    (el : lowerBox parent j cut=left) (er : upperBox parent j cut=right)
    (hl : l.verify f left=true) (hr : r.verify f right=true) :
    (Cover.split j cut l r).verify f parent=true := by
  simp only [Cover.verify,el,er,hl,hr,Bool.and_self]


end StableVotingDistortion.PaperBox
namespace StableVotingDistortion.PaperMiddle
open PaperBox
theorem rectLeaf {k l : Knot} {p P q Q z Z : ℚ}
    (h : fastCellAccept PaperCurve.fastHighSlope k l ⟨p,P⟩ ⟨q,Q⟩ ⟨z,Z⟩ = true) :
    RectWitness k l p P q Q z Z := ⟨.leaf,h⟩

theorem rectSplit0 {k l : Knot} {p P q Q z Z : ℚ} (cut : ℚ)
    (a : RectWitness k l p cut q Q z Z) (b : RectWitness k l cut P q Q z Z) :
    RectWitness k l p P q Q z Z := by
  obtain ⟨s,hs⟩ := a
  obtain ⟨t,ht⟩ := b
  refine ⟨.split 0 cut s t,verify_split_boxes 0 cut s t _ _ _ ?_ ?_ hs ht⟩ <;>
    funext i <;> fin_cases i <;> rfl

theorem rectSplit1 {k l : Knot} {p P q Q z Z : ℚ} (cut : ℚ)
    (a : RectWitness k l p P q cut z Z) (b : RectWitness k l p P cut Q z Z) :
    RectWitness k l p P q Q z Z := by
  obtain ⟨s,hs⟩ := a
  obtain ⟨t,ht⟩ := b
  refine ⟨.split 1 cut s t,verify_split_boxes 1 cut s t _ _ _ ?_ ?_ hs ht⟩ <;>
    funext i <;> fin_cases i <;> rfl

theorem rectSplit2 {k l : Knot} {p P q Q z Z : ℚ} (cut : ℚ)
    (a : RectWitness k l p P q Q z cut) (b : RectWitness k l p P q Q cut Z) :
    RectWitness k l p P q Q z Z := by
  obtain ⟨s,hs⟩ := a
  obtain ⟨t,ht⟩ := b
  refine ⟨.split 2 cut s t,verify_split_boxes 2 cut s t _ _ _ ?_ ?_ hs ht⟩ <;>
    funext i <;> fin_cases i <;> rfl


set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cell211_covered : CellCovered ⟨635,4826231,0⟩ ⟨640,4873392,0⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨635,4826231,0⟩ ⟨640,4873392,0⟩ (127/200) (16/25) 0 (703/1250) (127/200) 1 from
    (rectSplit2 (727/800) (rectSplit1 (703/2000) (rectSplit2 (4283/6400) (rectLeaf (by decide +kernel)) (rectSplit2 (41929/51200) (rectSplit1 (703/4000) (rectLeaf (by decide +kernel)) (rectSplit2 (312437/409600) (rectLeaf (by decide +kernel)) (rectSplit1 (9139/32000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (703/4000) (rectSplit2 (34463/40960) (rectLeaf (by decide +kernel)) (rectSplit2 (1392317/1638400) (rectLeaf (by decide +kernel)) (rectSplit2 (2881213/3276800) (rectSplit1 (703/6400) (rectLeaf (by decide +kernel)) (rectSplit2 (22759967/26214400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit1 (703/8000) (rectLeaf (by decide +kernel)) (rectSplit1 (2109/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))) (rectSplit2 (88457/102400) (rectSplit1 (703/3200) (rectLeaf (by decide +kernel)) (rectSplit1 (20387/64000) (rectSplit2 (693859/819200) (rectLeaf (by decide +kernel)) (rectSplit1 (34447/128000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (2109/8000) (rectSplit2 (730651/819200) (rectSplit1 (703/3200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (730651/819200) (rectSplit1 (4921/16000) (rectLeaf (by decide +kernel)) (rectSplit2 (5730233/6553600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (5159/6400) (rectSplit1 (9139/20000) (rectSplit2 (19541/25600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectSplit2 (9223/12800) (rectLeaf (by decide +kernel)) (rectSplit1 (7733/16000) (rectLeaf (by decide +kernel)) (rectSplit2 (79259/102400) (rectLeaf (by decide +kernel)) (rectSplit1 (68191/128000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))) (rectSplit2 (44557/51200) (rectSplit1 (9139/20000) (rectSplit2 (340031/409600) (rectLeaf (by decide +kernel)) (rectSplit1 (62567/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (1409399/1638400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (174943/204800) (rectSplit1 (20387/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectSplit1 (20387/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (7733/16000) (rectSplit1 (51319/128000) (rectSplit2 (180199/204800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) (rectSplit1 (703/2000) (rectSplit1 (703/4000) (rectSplit2 (6181/6400) (rectSplit1 (703/8000) (rectSplit2 (11997/12800) (rectLeaf (by decide +kernel)) (rectSplit1 (703/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (47623/51200) (rectLeaf (by decide +kernel)) (rectSplit1 (2109/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (2109/16000) (rectSplit1 (6327/64000) (rectSplit1 (18981/256000) (rectSplit2 (24943/25600) (rectLeaf (by decide +kernel)) (rectSplit1 (56943/1024000) (rectSplit2 (101743/102400) (rectSplit1 (170829/8192000) (rectSplit2 (808031/819200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (1527/1600) (rectSplit1 (4921/16000) (rectSplit1 (703/2560) (rectSplit2 (11997/12800) (rectSplit1 (28823/128000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (2109/8000) (rectSplit1 (13357/64000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectSplit1 (7733/16000) (rectSplit2 (6181/6400) (rectSplit2 (47623/51200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (1207/1280) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 211).take 1), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨635,4826231,0⟩,⟨640,4873392,0⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell211_covered ?_
  simp
