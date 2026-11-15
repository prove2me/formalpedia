-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells179To181
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:42:58.725886+00:00
-- url     : https://prove2.me/submissions/cdf1def2-7325-42cd-9e19-4c95f3f5f289

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
theorem cell179_covered : CellCovered ⟨475,3805653,1205219⟩ ⟨480,3821172,1198056⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨475,3805653,1205219⟩ ⟨480,3821172,1198056⟩ (19/40) (12/25) 0 (12/25) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (6/25) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (3/50) (rectLeaf (by decide +kernel)) (rectSplit2 (234121/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (3/20) (rectLeaf (by decide +kernel)) (rectSplit2 (1996043/2560000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))) (rectSplit2 (27419/40000) (rectSplit1 (33/100) (rectLeaf (by decide +kernel)) (rectSplit1 (309/800) (rectLeaf (by decide +kernel)) (rectSplit2 (204583/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (39/100) (rectSplit2 (114599/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (141/400) (rectSplit2 (990637/1280000) (rectLeaf (by decide +kernel)) (rectSplit1 (903/3200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit2 (24889/32000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) (rectSplit1 (3/10) (rectSplit1 (3/20) (rectSplit2 (137573/160000) (rectSplit1 (3/80) (rectLeaf (by decide +kernel)) (rectSplit1 (51/640) (rectLeaf (by decide +kernel)) (rectSplit2 (1075969/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (3/40) (rectSplit2 (280069/320000) (rectSplit1 (9/160) (rectSplit2 (2215937/2560000) (rectSplit1 (9/320) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (111043/128000) (rectSplit1 (33/320) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectSplit2 (28171/32000) (rectSplit2 (551933/640000) (rectSplit1 (39/160) (rectSplit1 (237/1280) (rectSplit2 (4312081/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (33/160) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (183/400) (rectSplit2 (28171/32000) (rectSplit1 (669/1600) (rectSplit2 (1092379/1280000) (rectSplit1 (4407/12800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectSplit1 (3/10) (rectSplit1 (21/80) (rectSplit2 (38359/40000) (rectSplit1 (21/160) (rectSplit1 (21/320) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (9453/10000) (rectSplit1 (87/200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell180_covered : CellCovered ⟨480,3821172,1198056⟩ ⟨485,3837592,1191008⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨480,3821172,1198056⟩ ⟨485,3837592,1191008⟩ (12/25) (97/200) 0 (97/200) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (97/400) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (97/1600) (rectLeaf (by decide +kernel)) (rectSplit2 (234121/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (97/640) (rectLeaf (by decide +kernel)) (rectSplit2 (1996043/2560000) (rectLeaf (by decide +kernel)) (rectSplit1 (1067/5120) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (27419/40000) (rectSplit1 (1067/3200) (rectLeaf (by decide +kernel)) (rectSplit1 (9991/25600) (rectLeaf (by decide +kernel)) (rectSplit2 (204583/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (291/800) (rectSplit2 (59761/80000) (rectLeaf (by decide +kernel)) (rectSplit2 (502703/640000) (rectLeaf (by decide +kernel)) (rectSplit1 (97/320) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (234121/320000) (rectLeaf (by decide +kernel)) (rectSplit2 (1996043/2560000) (rectLeaf (by decide +kernel)) (rectSplit1 (679/1600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))))) (rectSplit1 (97/320) (rectSplit1 (97/640) (rectSplit2 (137573/160000) (rectSplit1 (97/2560) (rectLeaf (by decide +kernel)) (rectSplit1 (1649/20480) (rectLeaf (by decide +kernel)) (rectSplit2 (266941/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (97/1280) (rectSplit2 (280069/320000) (rectSplit1 (291/5120) (rectSplit2 (1105507/1280000) (rectSplit1 (291/10240) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (1115353/1280000) (rectSplit1 (1067/10240) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectSplit2 (137573/160000) (rectSplit1 (1261/5120) (rectSplit1 (2037/10240) (rectSplit2 (1075969/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (1067/5120) (rectSplit2 (1105507/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectSplit1 (5917/12800) (rectSplit2 (28171/32000) (rectSplit1 (21631/51200) (rectSplit2 (1092379/1280000) (rectSplit1 (142493/409600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectSplit1 (97/320) (rectSplit1 (679/2560) (rectSplit2 (19453/20000) (rectSplit1 (679/5120) (rectSplit2 (72889/80000) (rectSplit1 (2037/40960) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (38359/40000) (rectSplit1 (2813/6400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell181_covered : CellCovered ⟨485,3837592,1191008⟩ ⟨490,3854925,1184054⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨485,3837592,1191008⟩ ⟨490,3854925,1184054⟩ (97/200) (49/100) 0 (49/100) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (49/200) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (147/1600) (rectLeaf (by decide +kernel)) (rectSplit2 (961099/1280000) (rectLeaf (by decide +kernel)) (rectSplit1 (2401/12800) (rectLeaf (by decide +kernel)) (rectSplit2 (8058017/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))) (rectSplit2 (27419/40000) (rectSplit1 (539/1600) (rectLeaf (by decide +kernel)) (rectSplit1 (5047/12800) (rectLeaf (by decide +kernel)) (rectSplit2 (204583/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (147/400) (rectSplit2 (59761/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (49/160) (rectSplit2 (502703/640000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (234121/320000) (rectLeaf (by decide +kernel)) (rectSplit2 (1996043/2560000) (rectLeaf (by decide +kernel)) (rectSplit1 (343/800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))))) (rectSplit1 (49/160) (rectSplit1 (49/320) (rectSplit2 (137573/160000) (rectSplit1 (49/1280) (rectLeaf (by decide +kernel)) (rectSplit1 (833/10240) (rectLeaf (by decide +kernel)) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectSplit1 (8869/81920) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) (rectSplit1 (49/640) (rectSplit2 (280069/320000) (rectSplit1 (147/2560) (rectSplit2 (1105507/1280000) (rectSplit1 (147/5120) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (1115353/1280000) (rectSplit1 (147/1280) (rectSplit2 (883421/1024000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectSplit2 (137573/160000) (rectSplit1 (637/2560) (rectSplit1 (1029/5120) (rectSplit2 (1075969/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (539/2560) (rectSplit2 (1105507/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectSplit1 (2989/6400) (rectSplit2 (28171/32000) (rectSplit2 (1115353/1280000) (rectSplit1 (833/2048) (rectSplit2 (2150297/2560000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectSplit1 (49/160) (rectSplit1 (343/1280) (rectSplit2 (19453/20000) (rectSplit1 (343/2048) (rectSplit2 (147419/160000) (rectSplit1 (343/4096) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (38359/40000) (rectSplit1 (1421/3200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 179).take 3), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨475,3805653,1205219⟩,⟨480,3821172,1198056⟩),(⟨480,3821172,1198056⟩,⟨485,3837592,1191008⟩),(⟨485,3837592,1191008⟩,⟨490,3854925,1184054⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell179_covered ?_
  refine slabCons cell180_covered ?_
  refine slabCons cell181_covered ?_
  simp
