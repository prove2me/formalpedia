-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells143To150
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:39:34.019384+00:00
-- url     : https://prove2.me/submissions/f25ba0a9-4e92-4bc0-a5e6-5560b150a2e0

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
theorem cell143_covered : CellCovered ⟨355,3723757,1325414⟩ ⟨356,3722198,1324774⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨355,3723757,1325414⟩ ⟨356,3722198,1324774⟩ (71/200) (89/250) 0 (89/250) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (89/400) (rectSplit2 (9983/16000) (rectLeaf (by decide +kernel)) (rectSplit2 (414089/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit1 (267/3200) (rectSplit2 (15835423/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (128854427/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (801/25600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (7555871/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (979/6400) (rectSplit2 (64065373/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (24889/32000) (rectSplit2 (214429/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (1157/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (267/1000) (rectSplit2 (137573/160000) (rectSplit1 (267/2000) (rectSplit1 (267/4000) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (8599547/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (69411751/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (267/32000) (rectSplit2 (139849127/163840000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (801/8000) (rectSplit2 (1105507/1280000) (rectSplit2 (8819441/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (70629373/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (801/64000) (rectSplit2 (565158059/655360000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (89/400) (rectSplit1 (89/3200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell144_covered : CellCovered ⟨356,3722198,1324774⟩ ⟨357,3720680,1324130⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨356,3722198,1324774⟩ ⟨357,3720680,1324130⟩ (89/250) (357/1000) 0 (357/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (357/1600) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (6590963/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (54416293/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (1071/12800) (rectSplit2 (253125541/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (2060464697/2621440000) (rectLeaf (by decide +kernel)) (rectSplit1 (3213/102400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (120652709/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (3927/25600) (rectSplit2 (1024322287/1310720000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))))))) (rectSplit2 (24889/32000) (rectSplit2 (892177/1280000) (rectSplit2 (6275891/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (1071/4000) (rectSplit2 (137573/160000) (rectSplit1 (1071/8000) (rectSplit1 (1071/16000) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (8599547/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (69411751/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (1071/128000) (rectSplit2 (139849127/163840000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (3213/32000) (rectSplit2 (1105507/1280000) (rectSplit2 (2206091/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (8829287/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (3213/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (357/1600) (rectSplit1 (357/12800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell145_covered : CellCovered ⟨357,3720680,1324130⟩ ⟨358,3719200,1323480⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨357,3720680,1324130⟩ ⟨358,3719200,1323480⟩ (357/1000) (179/500) 0 (179/500) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (179/800) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (6590963/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (54416293/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (537/6400) (rectSplit2 (253125541/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (2060464697/2621440000) (rectLeaf (by decide +kernel)) (rectSplit1 (1611/51200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (120652709/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (1969/12800) (rectSplit2 (1024322287/1310720000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))))))) (rectSplit2 (24889/32000) (rectSplit2 (892177/1280000) (rectSplit2 (6275891/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (537/2000) (rectSplit2 (137573/160000) (rectSplit1 (537/4000) (rectSplit1 (537/8000) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (8599547/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (69411751/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (537/64000) (rectSplit2 (560422133/655360000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (1611/16000) (rectSplit2 (1105507/1280000) (rectSplit2 (2206091/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (8829287/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (1611/128000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (179/800) (rectSplit1 (179/6400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell146_covered : CellCovered ⟨358,3719200,1323480⟩ ⟨359,3717760,1322825⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨358,3719200,1323480⟩ ⟨359,3717760,1322825⟩ (179/500) (359/1000) 0 (359/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (359/1600) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (6590963/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (54416293/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (1077/12800) (rectSplit2 (253125541/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (2060464697/2621440000) (rectLeaf (by decide +kernel)) (rectSplit1 (3231/102400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (120652709/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (3949/25600) (rectSplit2 (1024322287/1310720000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))))))) (rectSplit2 (24889/32000) (rectSplit2 (892177/1280000) (rectSplit2 (6275891/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (1077/4000) (rectSplit2 (137573/160000) (rectSplit1 (1077/8000) (rectSplit1 (1077/16000) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (8599547/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (17404219/20480000) (rectLeaf (by decide +kernel)) (rectSplit1 (1077/128000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (3231/32000) (rectSplit2 (1105507/1280000) (rectSplit2 (8829287/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (3231/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (359/1600) (rectSplit1 (359/12800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell147_covered : CellCovered ⟨359,3717760,1322825⟩ ⟨360,3716360,1322165⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨359,3717760,1322825⟩ ⟨360,3716360,1322165⟩ (359/1000) (9/25) 0 (9/25) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (9/40) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit1 (27/320) (rectSplit2 (15835423/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (128854427/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (81/2560) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (7555871/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (99/640) (rectSplit2 (64065373/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (24889/32000) (rectSplit2 (892177/1280000) (rectSplit2 (6275891/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (27/100) (rectSplit2 (137573/160000) (rectSplit1 (27/200) (rectSplit1 (27/400) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (2160143/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (17486269/20480000) (rectSplit2 (139274777/163840000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (81/800) (rectSplit2 (1105507/1280000) (rectSplit2 (8829287/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (81/6400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (9/40) (rectSplit1 (9/320) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell148_covered : CellCovered ⟨360,3716360,1322165⟩ ⟨361,3714999,1321500⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨360,3716360,1322165⟩ ⟨361,3714999,1321500⟩ (9/25) (361/1000) 0 (361/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (361/1600) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit1 (1083/12800) (rectSplit2 (15835423/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (128854427/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (1083/25600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (7555871/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (3971/25600) (rectSplit2 (64065373/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (24889/32000) (rectSplit2 (892177/1280000) (rectSplit2 (6275891/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (1083/4000) (rectSplit2 (137573/160000) (rectSplit1 (1083/8000) (rectSplit1 (1083/16000) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (2160143/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (17486269/20480000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (3249/32000) (rectSplit2 (1105507/1280000) (rectSplit2 (8829287/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (3249/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (361/2000) (rectLeaf (by decide +kernel)) (rectSplit2 (39453/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell149_covered : CellCovered ⟨361,3714999,1321500⟩ ⟨362,3713677,1320829⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨361,3714999,1321500⟩ ⟨362,3713677,1320829⟩ (361/1000) (181/500) 0 (181/500) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (181/800) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit1 (543/6400) (rectSplit2 (15835423/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (32394527/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (543/12800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (7555871/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (1991/12800) (rectSplit2 (64065373/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (24889/32000) (rectSplit2 (892177/1280000) (rectSplit2 (6275891/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (543/2000) (rectSplit2 (137573/160000) (rectSplit1 (543/4000) (rectSplit1 (543/8000) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (2160143/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (17486269/20480000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (1629/16000) (rectSplit2 (1105507/1280000) (rectSplit2 (8829287/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (1629/128000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (181/1000) (rectLeaf (by decide +kernel)) (rectSplit2 (39453/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell150_covered : CellCovered ⟨362,3713677,1320829⟩ ⟨363,3712395,1320154⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨362,3713677,1320829⟩ ⟨363,3712395,1320154⟩ (181/500) (363/1000) 0 (363/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (363/1600) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit1 (1089/12800) (rectSplit2 (15835423/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (32394527/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (1089/25600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (7555871/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (3993/25600) (rectSplit2 (64065373/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (24889/32000) (rectSplit2 (892177/1280000) (rectSplit2 (6275891/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (1089/4000) (rectSplit2 (137573/160000) (rectSplit1 (1089/8000) (rectSplit1 (1089/16000) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (2160143/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (17486269/20480000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (3267/32000) (rectSplit2 (1105507/1280000) (rectSplit2 (8829287/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (363/2000) (rectLeaf (by decide +kernel)) (rectSplit2 (39453/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 143).take 8), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨355,3723757,1325414⟩,⟨356,3722198,1324774⟩),(⟨356,3722198,1324774⟩,⟨357,3720680,1324130⟩),(⟨357,3720680,1324130⟩,⟨358,3719200,1323480⟩),(⟨358,3719200,1323480⟩,⟨359,3717760,1322825⟩),(⟨359,3717760,1322825⟩,⟨360,3716360,1322165⟩),(⟨360,3716360,1322165⟩,⟨361,3714999,1321500⟩),(⟨361,3714999,1321500⟩,⟨362,3713677,1320829⟩),(⟨362,3713677,1320829⟩,⟨363,3712395,1320154⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell143_covered ?_
  refine slabCons cell144_covered ?_
  refine slabCons cell145_covered ?_
  refine slabCons cell146_covered ?_
  refine slabCons cell147_covered ?_
  refine slabCons cell148_covered ?_
  refine slabCons cell149_covered ?_
  refine slabCons cell150_covered ?_
  simp
