-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells151To158
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:41:27.45092+00:00
-- url     : https://prove2.me/submissions/2c080dd3-7d48-4347-8075-3963bca303b8

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
theorem cell151_covered : CellCovered ⟨363,3712395,1320154⟩ ⟨364,3711151,1319473⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨363,3712395,1320154⟩ ⟨364,3711151,1319473⟩ (363/1000) (91/250) 0 (91/250) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (91/400) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit1 (273/3200) (rectSplit2 (15835423/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (32394527/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (273/6400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (7555871/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (1001/6400) (rectSplit2 (64065373/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (24889/32000) (rectSplit2 (892177/1280000) (rectSplit2 (6275891/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (637/2000) (rectSplit1 (4459/16000) (rectSplit2 (137573/160000) (rectSplit1 (4459/32000) (rectSplit1 (4459/64000) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (2160143/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (17486269/20480000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (13377/128000) (rectSplit2 (1105507/1280000) (rectSplit2 (8829287/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (91/500) (rectLeaf (by decide +kernel)) (rectSplit2 (39453/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell152_covered : CellCovered ⟨364,3711151,1319473⟩ ⟨365,3709946,1318787⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨364,3711151,1319473⟩ ⟨365,3709946,1318787⟩ (91/250) (73/200) 0 (73/200) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (73/320) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit1 (219/2560) (rectSplit2 (15835423/20480000) (rectLeaf (by decide +kernel)) (rectSplit1 (657/20480) (rectLeaf (by decide +kernel)) (rectSplit2 (32394527/40960000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (7555871/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (803/5120) (rectSplit2 (64065373/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (24889/32000) (rectSplit2 (164651/256000) (rectLeaf (by decide +kernel)) (rectSplit1 (949/3200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (511/1600) (rectSplit1 (3577/12800) (rectSplit2 (137573/160000) (rectSplit1 (3577/25600) (rectSplit1 (3577/51200) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (2160143/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (17486269/20480000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (10731/102400) (rectSplit2 (1105507/1280000) (rectSplit2 (8829287/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (73/400) (rectLeaf (by decide +kernel)) (rectSplit2 (39453/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell153_covered : CellCovered ⟨365,3709946,1318787⟩ ⟨366,3708781,1318096⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨365,3709946,1318787⟩ ⟨366,3708781,1318096⟩ (73/200) (183/500) 0 (183/500) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (183/800) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (6590963/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (54416293/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (549/6400) (rectSplit2 (253125541/327680000) (rectLeaf (by decide +kernel)) (rectSplit1 (1647/51200) (rectLeaf (by decide +kernel)) (rectSplit2 (103614241/131072000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (120652709/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (2013/12800) (rectSplit2 (103614241/131072000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))))))) (rectSplit2 (24889/32000) (rectSplit2 (164651/256000) (rectLeaf (by decide +kernel)) (rectSplit1 (2379/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (1281/4000) (rectSplit1 (8967/32000) (rectSplit1 (8967/64000) (rectSplit2 (69607/80000) (rectSplit2 (54701/64000) (rectSplit1 (26901/512000) (rectSplit2 (532241/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4331773/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (26901/512000) (rectSplit2 (551933/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4420387/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit2 (137573/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (183/1000) (rectLeaf (by decide +kernel)) (rectSplit2 (39453/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell154_covered : CellCovered ⟨366,3708781,1318096⟩ ⟨367,3707653,1317400⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨366,3708781,1318096⟩ ⟨367,3707653,1317400⟩ (183/500) (367/1000) 0 (367/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (367/1600) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (6590963/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (54416293/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (1101/12800) (rectSplit2 (253125541/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (103614241/131072000) (rectLeaf (by decide +kernel)) (rectSplit1 (3303/102400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (120652709/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (4037/25600) (rectSplit2 (103614241/131072000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))))))) (rectSplit2 (24889/32000) (rectSplit2 (164651/256000) (rectLeaf (by decide +kernel)) (rectSplit1 (4771/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (2569/8000) (rectSplit1 (17983/64000) (rectSplit1 (17983/128000) (rectSplit2 (69607/80000) (rectSplit2 (54701/64000) (rectSplit1 (53949/1024000) (rectSplit2 (532241/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4331773/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (53949/1024000) (rectSplit2 (551933/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4420387/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit2 (137573/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (367/2000) (rectLeaf (by decide +kernel)) (rectSplit2 (39453/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell155_covered : CellCovered ⟨367,3707653,1317400⟩ ⟨368,3706565,1316698⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨367,3707653,1317400⟩ ⟨368,3706565,1316698⟩ (367/1000) (46/125) 0 (46/125) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (23/100) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (6590963/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (54416293/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (69/800) (rectSplit2 (253125541/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (103614241/131072000) (rectLeaf (by decide +kernel)) (rectSplit1 (207/6400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (120652709/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (253/1600) (rectSplit2 (103614241/131072000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))))))) (rectSplit2 (24889/32000) (rectSplit2 (164651/256000) (rectLeaf (by decide +kernel)) (rectSplit1 (299/1000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (161/500) (rectSplit1 (1127/4000) (rectSplit1 (1127/8000) (rectSplit2 (69607/80000) (rectSplit2 (54701/64000) (rectSplit1 (3381/64000) (rectSplit2 (532241/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4331773/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (3381/64000) (rectSplit2 (551933/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4420387/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit2 (137573/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (23/125) (rectLeaf (by decide +kernel)) (rectSplit1 (69/200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell156_covered : CellCovered ⟨368,3706565,1316698⟩ ⟨369,3705515,1315991⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨368,3706565,1316698⟩ ⟨369,3705515,1315991⟩ (46/125) (369/1000) 0 (369/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (369/1600) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (6590963/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (54416293/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (1107/12800) (rectSplit2 (253125541/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (103614241/131072000) (rectLeaf (by decide +kernel)) (rectSplit1 (3321/102400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (120652709/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (4059/25600) (rectSplit2 (103614241/131072000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))))))) (rectSplit2 (24889/32000) (rectSplit2 (164651/256000) (rectLeaf (by decide +kernel)) (rectSplit1 (4797/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (2583/8000) (rectSplit1 (18081/64000) (rectSplit1 (18081/128000) (rectSplit2 (69607/80000) (rectSplit2 (54701/64000) (rectSplit1 (54243/1024000) (rectSplit2 (532241/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4331773/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (54243/1024000) (rectSplit2 (551933/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4420387/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit2 (137573/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (369/2000) (rectLeaf (by decide +kernel)) (rectSplit1 (1107/3200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell157_covered : CellCovered ⟨369,3705515,1315991⟩ ⟨370,3704504,1315279⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨369,3705515,1315991⟩ ⟨370,3704504,1315279⟩ (369/1000) (37/100) 0 (37/100) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (37/160) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (6590963/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (54416293/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (37/320) (rectSplit2 (494430959/655360000) (rectLeaf (by decide +kernel)) (rectSplit1 (111/1280) (rectSplit2 (1024322287/1310720000) (rectLeaf (by decide +kernel)) (rectSplit1 (111/2560) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit2 (494430959/655360000) (rectLeaf (by decide +kernel)) (rectSplit1 (407/2560) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))))) (rectSplit2 (24889/32000) (rectSplit2 (164651/256000) (rectLeaf (by decide +kernel)) (rectSplit1 (481/1600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (259/800) (rectSplit1 (1813/6400) (rectSplit1 (1813/12800) (rectSplit2 (69607/80000) (rectSplit2 (54701/64000) (rectSplit1 (5439/102400) (rectSplit2 (532241/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4331773/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (5439/102400) (rectSplit2 (551933/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4420387/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit2 (137573/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (111/400) (rectSplit1 (111/640) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell158_covered : CellCovered ⟨370,3704504,1315279⟩ ⟨375,3700022,1311638⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨370,3704504,1315279⟩ ⟨375,3700022,1311638⟩ (37/100) (3/8) 0 (3/8) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (15/64) (rectSplit2 (94907/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (793717/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (6590963/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (54416293/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (15/128) (rectSplit2 (494430959/655360000) (rectLeaf (by decide +kernel)) (rectSplit1 (45/512) (rectSplit2 (1024322287/1310720000) (rectLeaf (by decide +kernel)) (rectSplit1 (45/1024) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit2 (494430959/655360000) (rectLeaf (by decide +kernel)) (rectSplit1 (165/1024) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))))) (rectSplit2 (24889/32000) (rectSplit2 (892177/1280000) (rectSplit1 (165/512) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (21/64) (rectSplit1 (147/512) (rectSplit1 (147/1024) (rectSplit2 (69607/80000) (rectSplit2 (54701/64000) (rectSplit1 (147/2048) (rectSplit1 (147/4096) (rectSplit2 (532241/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4331773/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (441/8192) (rectSplit2 (551933/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4420387/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit2 (137573/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (9/32) (rectSplit1 (45/256) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 151).take 8), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨363,3712395,1320154⟩,⟨364,3711151,1319473⟩),(⟨364,3711151,1319473⟩,⟨365,3709946,1318787⟩),(⟨365,3709946,1318787⟩,⟨366,3708781,1318096⟩),(⟨366,3708781,1318096⟩,⟨367,3707653,1317400⟩),(⟨367,3707653,1317400⟩,⟨368,3706565,1316698⟩),(⟨368,3706565,1316698⟩,⟨369,3705515,1315991⟩),(⟨369,3705515,1315991⟩,⟨370,3704504,1315279⟩),(⟨370,3704504,1315279⟩,⟨375,3700022,1311638⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell151_covered ?_
  refine slabCons cell152_covered ?_
  refine slabCons cell153_covered ?_
  refine slabCons cell154_covered ?_
  refine slabCons cell155_covered ?_
  refine slabCons cell156_covered ?_
  refine slabCons cell157_covered ?_
  refine slabCons cell158_covered ?_
  simp
