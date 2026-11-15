-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells119To121
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:38:28.935204+00:00
-- url     : https://prove2.me/submissions/0ff804c8-5478-4cd2-8ad9-921264102c97

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
theorem cell119_covered : CellCovered ⟨331,3756318,1344890⟩ ⟨332,3755058,1343865⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨331,3756318,1344890⟩ ⟨332,3755058,1343865⟩ (331/1000) (83/250) 0 (83/250) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (83/400) (rectSplit2 (9983/16000) (rectLeaf (by decide +kernel)) (rectSplit2 (414089/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit2 (28052441/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (581/3200) (rectSplit2 (117275531/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (1743/12800) (rectSplit1 (5229/51200) (rectSplit2 (249748363/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (208917071/262144000) (rectSplit1 (15687/409600) (rectSplit2 (4132749517/5242880000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))))) (rectSplit2 (59761/80000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (249/1000) (rectSplit1 (747/8000) (rectSplit2 (69607/80000) (rectSplit2 (54701/64000) (rectSplit1 (747/16000) (rectSplit2 (2173271/2560000) (rectSplit2 (3456557/4096000) (rectSplit2 (133196513/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (2241/128000) (rectSplit2 (1101032473/1310720000) (rectSplit2 (8560037201/10485760000) (rectLeaf (by decide +kernel)) (rectSplit2 (70217855689/83886080000) (rectSplit2 (560005287431/671088640000) (rectSplit2 (2203532430023/2684354560000) (rectLeaf (by decide +kernel)) (rectSplit2 (1784719175839/2147483648000) (rectSplit2 (14168287247609/17179869184000) (rectLeaf (by decide +kernel)) (rectSplit2 (28446040654321/34359738368000) (rectSplit1 (2241/1024000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (442531/512000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit2 (137573/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (83/400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell120_covered : CellCovered ⟨332,3755058,1343865⟩ ⟨333,3753798,1342841⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨332,3755058,1343865⟩ ⟨333,3753798,1342841⟩ (83/250) (333/1000) 0 (333/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (333/1600) (rectSplit2 (9983/16000) (rectLeaf (by decide +kernel)) (rectSplit2 (414089/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit2 (28052441/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (2331/12800) (rectSplit2 (117275531/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (6993/51200) (rectSplit1 (20979/204800) (rectSplit2 (249748363/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (208917071/262144000) (rectSplit1 (62937/1638400) (rectSplit2 (4132749517/5242880000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))))) (rectSplit2 (59761/80000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (999/4000) (rectSplit1 (2997/32000) (rectSplit2 (69607/80000) (rectSplit2 (54701/64000) (rectSplit1 (2997/64000) (rectSplit2 (2173271/2560000) (rectSplit2 (3456557/4096000) (rectSplit2 (133196513/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (8991/512000) (rectSplit2 (1070637871/1310720000) (rectLeaf (by decide +kernel)) (rectSplit2 (8813325551/10485760000) (rectSplit2 (2810335273/3355443200) (rectSplit2 (560329496519/671088640000) (rectSplit2 (17638634131/21474836480) (rectLeaf (by decide +kernel)) (rectSplit2 (8855805785201/10737418240000) (rectLeaf (by decide +kernel)) (rectSplit1 (8991/4096000) (rectSplit2 (3564215545901/4294967296000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (551933/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2222501/2560000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectSplit2 (137573/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (333/1600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell121_covered : CellCovered ⟨333,3753798,1342841⟩ ⟨334,3752534,1341921⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨333,3753798,1342841⟩ ⟨334,3752534,1341921⟩ (333/1000) (167/500) 0 (167/500) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (167/800) (rectSplit2 (9983/16000) (rectLeaf (by decide +kernel)) (rectSplit2 (414089/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit2 (28052441/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (1169/6400) (rectSplit2 (117275531/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (3507/25600) (rectSplit2 (983796151/1310720000) (rectLeaf (by decide +kernel)) (rectSplit1 (3507/51200) (rectSplit2 (2043578807/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (16576589971/20971520000) (rectLeaf (by decide +kernel)) (rectSplit1 (3507/409600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))))) (rectSplit2 (59761/80000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (501/2000) (rectSplit1 (1503/16000) (rectSplit2 (69607/80000) (rectSplit2 (54701/64000) (rectSplit1 (1503/32000) (rectSplit2 (2173271/2560000) (rectSplit2 (16662487/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (138365663/163840000) (rectSplit1 (4509/256000) (rectSplit2 (214292987/262144000) (rectLeaf (by decide +kernel)) (rectSplit2 (8819942063/10485760000) (rectSplit2 (70311313921/83886080000) (rectSplit2 (276032581441/335544320000) (rectLeaf (by decide +kernel)) (rectSplit2 (1109343000007/1342177280000) (rectLeaf (by decide +kernel)) (rectSplit2 (896857213643/1073741824000) (rectSplit2 (7127943640957/8589934592000) (rectLeaf (by decide +kernel)) (rectSplit1 (4509/2048000) (rectSplit2 (14302801350101/17179869184000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (551933/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2222501/2560000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectSplit2 (137573/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (167/800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 119).take 3), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨331,3756318,1344890⟩,⟨332,3755058,1343865⟩),(⟨332,3755058,1343865⟩,⟨333,3753798,1342841⟩),(⟨333,3753798,1342841⟩,⟨334,3752534,1341921⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell119_covered ?_
  refine slabCons cell120_covered ?_
  refine slabCons cell121_covered ?_
  simp
