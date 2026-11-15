-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells054To059
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:37:25.526683+00:00
-- url     : https://prove2.me/submissions/c7cb2346-e507-443a-a112-4022198a8e1a

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
theorem cell054_covered : CellCovered ⟨266,3897034,1413378⟩ ⟨267,3893775,1412293⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨266,3897034,1413378⟩ ⟨267,3893775,1412293⟩ (133/500) (267/1000) 0 (267/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (1869/8000) (rectSplit1 (13083/64000) (rectSplit1 (39249/256000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (117747/2048000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (801/8000) (rectSplit2 (24889/32000) (rectLeaf (by decide +kernel)) (rectSplit2 (40807/51200) (rectSplit2 (801371/1024000) (rectLeaf (by decide +kernel)) (rectSplit2 (6484813/8192000) (rectSplit2 (51656969/65536000) (rectSplit2 (206258651/262144000) (rectSplit2 (1642315483/2097152000) (rectLeaf (by decide +kernel)) (rectSplit1 (801/64000) (rectSplit2 (13146277589/16777216000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (267/1600) (rectSplit2 (137573/160000) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell055_covered : CellCovered ⟨267,3893775,1412293⟩ ⟨268,3890550,1411203⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨267,3893775,1412293⟩ ⟨268,3890550,1411203⟩ (267/1000) (67/250) 0 (67/250) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (201/2000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (201/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (204583/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (2613/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (201/2000) (rectSplit2 (131009/160000) (rectSplit2 (515831/640000) (rectSplit2 (4003573/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (32643959/40960000) (rectSplit2 (259305547/327680000) (rectSplit2 (2052906251/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (16530940633/20971520000) (rectSplit1 (201/16000) (rectSplit2 (65800690657/83886080000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (68513/80000) (rectLeaf (by decide +kernel)) (rectSplit2 (559591/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (5039591/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))) using 1 <;> decide +kernel

theorem cell056_covered : CellCovered ⟨268,3890550,1411203⟩ ⟨269,3887358,1410110⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨268,3890550,1411203⟩ ⟨269,3887358,1410110⟩ (67/250) (269/1000) 0 (269/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (807/8000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (807/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (204583/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (10491/64000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (807/8000) (rectSplit2 (131009/160000) (rectSplit2 (515831/640000) (rectSplit2 (4003573/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (32643959/40960000) (rectSplit2 (129960461/163840000) (rectSplit2 (517995719/655360000) (rectSplit2 (4105197127/5242880000) (rectLeaf (by decide +kernel)) (rectSplit1 (807/64000) (rectSplit2 (32880345641/41943040000) (rectLeaf (by decide +kernel)) (rectSplit2 (66032071657/83886080000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (68513/80000) (rectLeaf (by decide +kernel)) (rectSplit2 (559591/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (5039591/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))) using 1 <;> decide +kernel

theorem cell057_covered : CellCovered ⟨269,3887358,1410110⟩ ⟨270,3884851,1408880⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨269,3887358,1410110⟩ ⟨270,3884851,1408880⟩ (269/1000) (27/100) 0 (27/100) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (81/800) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (81/1600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (204583/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (1053/6400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (81/800) (rectSplit2 (131009/160000) (rectSplit2 (515831/640000) (rectSplit2 (4003573/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (32643959/40960000) (rectSplit2 (129960461/163840000) (rectSplit2 (1026760813/1310720000) (rectLeaf (by decide +kernel)) (rectSplit2 (4145811877/5242880000) (rectSplit2 (16544478883/20971520000) (rectSplit1 (243/3200) (rectSplit2 (65828997907/83886080000) (rectLeaf (by decide +kernel)) (rectSplit1 (243/25600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (68513/80000) (rectLeaf (by decide +kernel)) (rectSplit2 (559591/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (5039591/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))) using 1 <;> decide +kernel

theorem cell058_covered : CellCovered ⟨270,3884851,1408880⟩ ⟨271,3881872,1407749⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨270,3884851,1408880⟩ ⟨271,3881872,1407749⟩ (27/100) (271/1000) 0 (271/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (813/8000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (813/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (204583/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (10569/64000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (813/8000) (rectSplit2 (131009/160000) (rectSplit2 (515831/640000) (rectSplit2 (4003573/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (16383517/20480000) (rectSplit2 (65164843/81920000) (rectSplit2 (259551697/327680000) (rectSplit2 (2053152401/2621440000) (rectLeaf (by decide +kernel)) (rectSplit1 (813/64000) (rectSplit2 (16448480383/20971520000) (rectLeaf (by decide +kernel)) (rectSplit2 (33059788991/41943040000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (68513/80000) (rectLeaf (by decide +kernel)) (rectSplit2 (559591/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (5039591/5120000) (rectLeaf (by decide +kernel)) (rectSplit1 (1897/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))))) using 1 <;> decide +kernel

theorem cell059_covered : CellCovered ⟨271,3881872,1407749⟩ ⟨272,3878795,1406641⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨271,3881872,1407749⟩ ⟨272,3878795,1406641⟩ (271/1000) (34/125) 0 (34/125) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (51/500) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (51/1000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (204583/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (663/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (51/500) (rectSplit2 (131009/160000) (rectSplit2 (515831/640000) (rectSplit2 (4003573/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (16383517/20480000) (rectSplit2 (65164843/81920000) (rectSplit2 (259551697/327680000) (rectSplit2 (2053152401/2621440000) (rectLeaf (by decide +kernel)) (rectSplit1 (51/4000) (rectSplit2 (16448480383/20971520000) (rectLeaf (by decide +kernel)) (rectSplit2 (33059788991/41943040000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (68513/80000) (rectLeaf (by decide +kernel)) (rectSplit2 (559591/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (5039591/5120000) (rectLeaf (by decide +kernel)) (rectSplit1 (119/500) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 54).take 6), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨266,3897034,1413378⟩,⟨267,3893775,1412293⟩),(⟨267,3893775,1412293⟩,⟨268,3890550,1411203⟩),(⟨268,3890550,1411203⟩,⟨269,3887358,1410110⟩),(⟨269,3887358,1410110⟩,⟨270,3884851,1408880⟩),(⟨270,3884851,1408880⟩,⟨271,3881872,1407749⟩),(⟨271,3881872,1407749⟩,⟨272,3878795,1406641⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell054_covered ?_
  refine slabCons cell055_covered ?_
  refine slabCons cell056_covered ?_
  refine slabCons cell057_covered ?_
  refine slabCons cell058_covered ?_
  refine slabCons cell059_covered ?_
  simp
