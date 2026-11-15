-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells092To093
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:38:01.339919+00:00
-- url     : https://prove2.me/submissions/ae6940b6-426c-4f0d-a860-d2e1ccc5489a

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
theorem cell092_covered : CellCovered ⟨304,3798271,1372829⟩ ⟨305,3796301,1371810⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨304,3798271,1372829⟩ ⟨305,3796301,1371810⟩ (38/125) (61/200) 0 (61/200) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (61/400) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (61/800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (671/3200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (61/400) (rectSplit1 (61/640) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (526771/640000) (rectSplit1 (183/5120) (rectSplit2 (2033239/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (8206801/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (33491809/40960000) (rectSplit2 (133302631/163840000) (rectSplit2 (1056451973/1310720000) (rectLeaf (by decide +kernel)) (rectSplit1 (183/40960) (rectSplit2 (2122873021/2621440000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (61/400) (rectSplit2 (138667/160000) (rectSplit2 (1094567/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (427/1600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell093_covered : CellCovered ⟨305,3796301,1371810⟩ ⟨306,3794368,1370786⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨305,3796301,1371810⟩ ⟨306,3794368,1370786⟩ (61/200) (153/500) 0 (153/500) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (153/1000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (153/2000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (1683/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (153/1000) (rectSplit1 (153/1600) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (526771/640000) (rectSplit1 (459/12800) (rectSplit2 (2033239/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (8206801/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (33491809/40960000) (rectSplit1 (459/51200) (rectSplit2 (264611447/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (2133506701/2621440000) (rectSplit2 (17018208233/20971520000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (153/1000) (rectSplit2 (138667/160000) (rectSplit2 (1094567/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (1071/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 92).take 2), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨304,3798271,1372829⟩,⟨305,3796301,1371810⟩),(⟨305,3796301,1371810⟩,⟨306,3794368,1370786⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell092_covered ?_
  refine slabCons cell093_covered ?_
  simp
