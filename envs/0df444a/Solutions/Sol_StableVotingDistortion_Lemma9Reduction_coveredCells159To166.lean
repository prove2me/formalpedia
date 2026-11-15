-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells159To166
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:41:29.59521+00:00
-- url     : https://prove2.me/submissions/44373f25-6d7a-49e7-a617-2f75b940ee86

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
theorem cell159_covered : CellCovered ⟨375,3700022,1311638⟩ ⟨380,3696492,1307864⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨375,3700022,1311638⟩ ⟨380,3696492,1307864⟩ (3/8) (19/50) 0 (19/50) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (19/80) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (6590963/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (54416293/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (19/160) (rectSplit2 (494430959/655360000) (rectLeaf (by decide +kernel)) (rectSplit1 (57/640) (rectSplit2 (4132749517/5242880000) (rectLeaf (by decide +kernel)) (rectSplit1 (57/1280) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit2 (494430959/655360000) (rectLeaf (by decide +kernel)) (rectSplit1 (209/1280) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))))) (rectSplit2 (24889/32000) (rectSplit2 (892177/1280000) (rectSplit1 (209/640) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (133/400) (rectSplit1 (133/800) (rectSplit2 (137573/160000) (rectSplit1 (133/1600) (rectSplit1 (133/3200) (rectSplit2 (266941/320000) (rectLeaf (by decide +kernel)) (rectSplit2 (2176553/2560000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (399/6400) (rectSplit2 (1105507/1280000) (rectSplit2 (8829287/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (33983/40000) (rectSplit1 (1197/6400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (57/200) (rectSplit1 (57/400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell160_covered : CellCovered ⟨380,3696492,1307864⟩ ⟨385,3693906,1303953⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨380,3696492,1307864⟩ ⟨385,3693906,1303953⟩ (19/50) (77/200) 0 (77/200) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (77/320) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (6590963/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (77/640) (rectSplit2 (31429619/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (231/5120) (rectLeaf (by decide +kernel)) (rectSplit2 (64547827/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (2974103/4096000) (rectLeaf (by decide +kernel)) (rectSplit2 (25481413/32768000) (rectLeaf (by decide +kernel)) (rectSplit1 (847/5120) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))))) (rectSplit2 (24889/32000) (rectSplit2 (892177/1280000) (rectSplit1 (847/2560) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (539/1600) (rectSplit1 (539/3200) (rectSplit2 (137573/160000) (rectSplit1 (539/5120) (rectSplit1 (539/10240) (rectSplit2 (525677/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4328491/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (539/6400) (rectSplit2 (1105507/1280000) (rectSplit2 (8829287/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (33983/40000) (rectSplit1 (4851/25600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (231/800) (rectSplit1 (231/1600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell161_covered : CellCovered ⟨385,3693906,1303953⟩ ⟨390,3692259,1299903⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨385,3693906,1303953⟩ ⟨390,3692259,1299903⟩ (77/200) (39/100) 0 (39/100) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (39/160) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (6590963/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (39/320) (rectSplit2 (31429619/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (117/2560) (rectLeaf (by decide +kernel)) (rectSplit2 (64547827/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (2974103/4096000) (rectLeaf (by decide +kernel)) (rectSplit1 (117/640) (rectSplit2 (64547827/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (24889/32000) (rectSplit2 (892177/1280000) (rectSplit1 (429/1280) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (273/800) (rectSplit1 (273/1600) (rectSplit2 (137573/160000) (rectSplit1 (273/2560) (rectSplit1 (273/5120) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (8681597/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (273/3200) (rectSplit2 (1105507/1280000) (rectSplit2 (8829287/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (33983/40000) (rectSplit1 (273/1280) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (117/400) (rectSplit1 (351/3200) (rectSplit2 (39453/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell162_covered : CellCovered ⟨390,3692259,1299903⟩ ⟨395,3691545,1295711⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨390,3692259,1299903⟩ ⟨395,3691545,1295711⟩ (39/100) (79/200) 0 (79/200) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (79/320) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (6590963/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (79/640) (rectSplit2 (31429619/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (237/5120) (rectLeaf (by decide +kernel)) (rectSplit2 (64547827/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (2974103/4096000) (rectLeaf (by decide +kernel)) (rectSplit1 (237/1280) (rectSplit2 (64547827/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (1000483/1280000) (rectSplit2 (6797729/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (1027/3200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))) (rectSplit1 (553/1600) (rectSplit1 (553/3200) (rectSplit2 (137573/160000) (rectSplit1 (553/5120) (rectSplit1 (553/8192) (rectSplit2 (1075969/1280000) (rectSplit1 (1659/65536) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (553/6400) (rectSplit2 (1105507/1280000) (rectSplit2 (8829287/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (33983/40000) (rectSplit1 (553/2560) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (237/800) (rectSplit1 (711/6400) (rectSplit2 (39453/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell163_covered : CellCovered ⟨395,3691545,1295711⟩ ⟨400,3691762,1291376⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨395,3691545,1295711⟩ ⟨400,3691762,1291376⟩ (79/200) (2/5) 0 (2/5) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (1/4) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (6590963/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (1/8) (rectSplit2 (31429619/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (1/16) (rectLeaf (by decide +kernel)) (rectSplit2 (64547827/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (2974103/4096000) (rectLeaf (by decide +kernel)) (rectSplit1 (3/16) (rectSplit2 (64547827/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (1000483/1280000) (rectSplit2 (7280183/10240000) (rectSplit1 (13/40) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectSplit1 (7/20) (rectSplit1 (7/40) (rectSplit2 (137573/160000) (rectSplit1 (7/64) (rectSplit1 (35/512) (rectSplit2 (542087/640000) (rectSplit1 (35/1024) (rectSplit2 (4262851/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (7/80) (rectSplit2 (1105507/1280000) (rectSplit2 (8829287/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (33983/40000) (rectSplit1 (7/32) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (3/10) (rectSplit1 (9/80) (rectSplit2 (39453/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell164_covered : CellCovered ⟨400,3691762,1291376⟩ ⟨405,3692765,1286847⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨400,3691762,1291376⟩ ⟨405,3692765,1286847⟩ (2/5) (81/200) 0 (81/200) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (81/320) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit1 (81/640) (rectSplit2 (3898549/5120000) (rectLeaf (by decide +kernel)) (rectSplit1 (81/1280) (rectLeaf (by decide +kernel)) (rectSplit2 (32394527/40960000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (7073417/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (15352969/20480000) (rectLeaf (by decide +kernel)) (rectSplit1 (891/5120) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (114599/160000) (rectSplit2 (204583/320000) (rectSplit1 (891/2560) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (990637/1280000) (rectLeaf (by decide +kernel)) (rectSplit1 (3969/12800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) (rectSplit1 (567/1600) (rectSplit1 (567/3200) (rectSplit2 (137573/160000) (rectSplit1 (567/5120) (rectSplit1 (567/8192) (rectSplit2 (525677/640000) (rectLeaf (by decide +kernel)) (rectSplit1 (567/16384) (rectSplit2 (4328491/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (567/6400) (rectSplit2 (1105507/1280000) (rectSplit1 (567/51200) (rectSplit2 (8829287/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (137573/160000) (rectSplit1 (6237/25600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (243/800) (rectSplit1 (729/6400) (rectSplit2 (39453/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell165_covered : CellCovered ⟨405,3692765,1286847⟩ ⟨410,3694636,1282147⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨405,3692765,1286847⟩ ⟨410,3694636,1282147⟩ (81/200) (41/100) 0 (41/100) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (41/160) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit1 (41/320) (rectSplit2 (3898549/5120000) (rectLeaf (by decide +kernel)) (rectSplit1 (41/640) (rectLeaf (by decide +kernel)) (rectSplit2 (32394527/40960000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (7073417/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (15352969/20480000) (rectLeaf (by decide +kernel)) (rectSplit1 (451/2560) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (114599/160000) (rectSplit2 (204583/320000) (rectSplit1 (451/1280) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (990637/1280000) (rectLeaf (by decide +kernel)) (rectSplit1 (533/1600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) (rectSplit1 (287/800) (rectSplit1 (287/1600) (rectSplit2 (137573/160000) (rectSplit1 (287/2560) (rectSplit1 (287/4096) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectSplit1 (861/32768) (rectSplit2 (4361311/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (287/3200) (rectSplit2 (111043/128000) (rectSplit1 (287/12800) (rectSplit2 (2206091/2560000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (69607/80000) (rectSplit1 (861/3200) (rectSplit2 (134291/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (123/400) (rectSplit1 (369/3200) (rectSplit2 (39453/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell166_covered : CellCovered ⟨410,3694636,1282147⟩ ⟨415,3697434,1277291⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨410,3694636,1282147⟩ ⟨415,3697434,1277291⟩ (41/100) (83/200) 0 (83/200) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (83/320) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit1 (83/640) (rectSplit2 (3898549/5120000) (rectLeaf (by decide +kernel)) (rectSplit1 (83/1024) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (7073417/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (62618011/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (913/5120) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (114599/160000) (rectSplit2 (842947/1280000) (rectSplit1 (913/2560) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (990637/1280000) (rectLeaf (by decide +kernel)) (rectSplit1 (1079/3200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) (rectSplit1 (581/1600) (rectSplit1 (581/3200) (rectSplit2 (137573/160000) (rectSplit1 (581/5120) (rectSplit1 (581/8192) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectSplit1 (581/32768) (rectLeaf (by decide +kernel)) (rectSplit2 (2160143/2560000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (581/6400) (rectSplit1 (1743/25600) (rectSplit2 (1105507/1280000) (rectSplit2 (8829287/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (69607/80000) (rectSplit1 (1743/6400) (rectSplit2 (134291/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (249/800) (rectSplit1 (747/6400) (rectSplit2 (39453/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 159).take 8), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨375,3700022,1311638⟩,⟨380,3696492,1307864⟩),(⟨380,3696492,1307864⟩,⟨385,3693906,1303953⟩),(⟨385,3693906,1303953⟩,⟨390,3692259,1299903⟩),(⟨390,3692259,1299903⟩,⟨395,3691545,1295711⟩),(⟨395,3691545,1295711⟩,⟨400,3691762,1291376⟩),(⟨400,3691762,1291376⟩,⟨405,3692765,1286847⟩),(⟨405,3692765,1286847⟩,⟨410,3694636,1282147⟩),(⟨410,3694636,1282147⟩,⟨415,3697434,1277291⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell159_covered ?_
  refine slabCons cell160_covered ?_
  refine slabCons cell161_covered ?_
  refine slabCons cell162_covered ?_
  refine slabCons cell163_covered ?_
  refine slabCons cell164_covered ?_
  refine slabCons cell165_covered ?_
  refine slabCons cell166_covered ?_
  simp
