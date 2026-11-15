-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells198To199
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:43:58.996719+00:00
-- url     : https://prove2.me/submissions/cb9c769f-a686-460d-b59c-e20bc251edf8

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
theorem cell198_covered : CellCovered ⟨570,4273080,1073241⟩ ⟨575,4311633,1063892⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨570,4273080,1073241⟩ ⟨575,4311633,1063892⟩ (57/100) (23/40) 0 (703/1250) (57/100) 1 from
    (rectSplit2 (357/400) (rectSplit1 (703/2000) (rectSplit2 (2469/3200) (rectSplit2 (15237/25600) (rectLeaf (by decide +kernel)) (rectSplit1 (703/4000) (rectLeaf (by decide +kernel)) (rectSplit1 (9139/32000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (703/4000) (rectSplit2 (10263/12800) (rectLeaf (by decide +kernel)) (rectSplit2 (16653/20480) (rectLeaf (by decide +kernel)) (rectSplit2 (141351/163840) (rectSplit1 (703/16000) (rectLeaf (by decide +kernel)) (rectSplit1 (4921/64000) (rectLeaf (by decide +kernel)) (rectSplit2 (54915/65536) (rectLeaf (by decide +kernel)) (rectSplit1 (58349/512000) (rectLeaf (by decide +kernel)) (rectSplit1 (561697/4096000) (rectLeaf (by decide +kernel)) (rectSplit2 (2253489/2621440) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))))) (rectSplit1 (703/16000) (rectLeaf (by decide +kernel)) (rectSplit1 (4921/64000) (rectLeaf (by decide +kernel)) (rectSplit1 (9139/102400) (rectLeaf (by decide +kernel)) (rectSplit2 (2900163/3276800) (rectSplit1 (498427/4096000) (rectLeaf (by decide +kernel)) (rectSplit2 (22835589/26214400) (rectSplit1 (5094641/32768000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))))))) (rectSplit2 (21687/25600) (rectSplit1 (703/3200) (rectLeaf (by decide +kernel)) (rectSplit1 (34447/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (41439/51200) (rectLeaf (by decide +kernel)) (rectSplit1 (328301/1024000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) (rectSplit1 (2109/8000) (rectSplit2 (181623/204800) (rectSplit2 (355119/409600) (rectSplit1 (703/3200) (rectSplit2 (2816571/3276800) (rectLeaf (by decide +kernel)) (rectSplit1 (6327/32000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (1412349/1638400) (rectLeaf (by decide +kernel)) (rectSplit1 (7733/32000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (703/3200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit2 (179301/204800) (rectSplit2 (352797/409600) (rectSplit1 (18981/64000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectSplit1 (18981/64000) (rectLeaf (by decide +kernel)) (rectSplit1 (155363/512000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))))))) (rectSplit2 (1299/1600) (rectSplit2 (2211/3200) (rectSplit1 (9139/20000) (rectLeaf (by decide +kernel)) (rectSplit2 (15753/25600) (rectLeaf (by decide +kernel)) (rectSplit2 (33441/51200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (9139/20000) (rectSplit2 (4809/6400) (rectLeaf (by decide +kernel)) (rectSplit2 (2001/2560) (rectLeaf (by decide +kernel)) (rectSplit1 (16169/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (4809/6400) (rectSplit1 (83657/160000) (rectSplit1 (324083/640000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (7733/16000) (rectLeaf (by decide +kernel)) (rectSplit2 (39633/51200) (rectLeaf (by decide +kernel)) (rectSplit1 (68191/128000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))))) (rectSplit1 (7733/16000) (rectSplit2 (2259/2560) (rectSplit2 (87651/102400) (rectSplit1 (13357/32000) (rectSplit1 (96311/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (13357/32000) (rectSplit2 (353313/409600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit2 (10779/12800) (rectLeaf (by decide +kernel)) (rectSplit2 (22203/25600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))) (rectSplit1 (703/2000) (rectSplit1 (703/4000) (rectSplit2 (3157/3200) (rectSplit2 (6013/6400) (rectSplit1 (703/8000) (rectSplit2 (46599/51200) (rectLeaf (by decide +kernel)) (rectSplit2 (377307/409600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (46599/51200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit1 (703/6400) (rectSplit2 (49007/51200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit2 (3071/3200) (rectSplit1 (4921/16000) (rectSplit2 (5927/6400) (rectSplit1 (7733/32000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (42883/80000) (rectSplit1 (328301/640000) (rectSplit2 (3071/3200) (rectSplit1 (553261/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell199_covered : CellCovered ⟨575,4311633,1063892⟩ ⟨580,4351160,1054640⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨575,4311633,1063892⟩ ⟨580,4351160,1054640⟩ (23/40) (29/50) 0 (703/1250) (23/40) 1 from
    (rectSplit2 (143/160) (rectSplit1 (703/2000) (rectSplit2 (991/1280) (rectSplit1 (703/8000) (rectLeaf (by decide +kernel)) (rectSplit1 (703/3200) (rectLeaf (by decide +kernel)) (rectSplit1 (7733/25600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (703/4000) (rectSplit2 (4117/5120) (rectLeaf (by decide +kernel)) (rectSplit2 (6679/8192) (rectLeaf (by decide +kernel)) (rectSplit2 (56645/65536) (rectSplit1 (703/16000) (rectLeaf (by decide +kernel)) (rectSplit1 (4921/64000) (rectLeaf (by decide +kernel)) (rectSplit2 (110077/131072) (rectLeaf (by decide +kernel)) (rectSplit1 (58349/512000) (rectLeaf (by decide +kernel)) (rectSplit1 (561697/4096000) (rectLeaf (by decide +kernel)) (rectSplit2 (903107/1048576) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))))) (rectSplit1 (2109/32000) (rectLeaf (by decide +kernel)) (rectSplit1 (11951/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (462799/524288) (rectSplit1 (34447/256000) (rectLeaf (by decide +kernel)) (rectSplit2 (1822279/2097152) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (8693/10240) (rectSplit1 (703/3200) (rectLeaf (by decide +kernel)) (rectSplit2 (64189/81920) (rectLeaf (by decide +kernel)) (rectSplit1 (16169/64000) (rectLeaf (by decide +kernel)) (rectSplit2 (133733/163840) (rectLeaf (by decide +kernel)) (rectSplit1 (160987/512000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))) (rectSplit1 (2109/8000) (rectSplit2 (72757/81920) (rectSplit2 (142301/163840) (rectSplit1 (703/3200) (rectSplit2 (565991/655360) (rectSplit1 (6327/32000) (rectLeaf (by decide +kernel)) (rectSplit2 (4518289/5242880) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit2 (1128769/1310720) (rectLeaf (by decide +kernel)) (rectSplit1 (7733/32000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (703/3200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit2 (36149/40960) (rectSplit2 (57563/65536) (rectSplit2 (565991/655360) (rectSplit1 (20387/64000) (rectSplit1 (37259/128000) (rectSplit2 (4518289/5242880) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (18981/64000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))))) (rectSplit2 (521/640) (rectSplit2 (889/1280) (rectSplit1 (9139/20000) (rectLeaf (by decide +kernel)) (rectSplit2 (6347/10240) (rectLeaf (by decide +kernel)) (rectSplit2 (13459/20480) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (9139/20000) (rectSplit2 (1931/2560) (rectLeaf (by decide +kernel)) (rectSplit2 (15907/20480) (rectLeaf (by decide +kernel)) (rectSplit1 (16169/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (1931/2560) (rectSplit1 (83657/160000) (rectSplit1 (324083/640000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (7733/16000) (rectLeaf (by decide +kernel)) (rectSplit2 (16213/20480) (rectSplit1 (68191/128000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))))) (rectSplit1 (7733/16000) (rectSplit2 (905/1024) (rectSplit2 (35129/40960) (rectSplit1 (13357/32000) (rectSplit1 (96311/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (13357/32000) (rectSplit2 (141587/163840) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit2 (4423/5120) (rectSplit2 (34109/40960) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) (rectSplit1 (703/2000) (rectSplit1 (703/4000) (rectSplit2 (303/320) (rectSplit1 (703/8000) (rectSplit2 (589/640) (rectSplit1 (703/12800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (589/640) (rectSplit2 (461/512) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (2109/16000) (rectSplit2 (2509/2560) (rectSplit1 (2109/32000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (1229/1280) (rectSplit2 (4831/5120) (rectSplit1 (2109/8000) (rectSplit2 (18559/20480) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (42883/80000) (rectSplit2 (1263/1280) (rectSplit1 (11951/25600) (rectSplit2 (939/1024) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 198).take 2), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨570,4273080,1073241⟩,⟨575,4311633,1063892⟩),(⟨575,4311633,1063892⟩,⟨580,4351160,1054640⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell198_covered ?_
  refine slabCons cell199_covered ?_
  simp
