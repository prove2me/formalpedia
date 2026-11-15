-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells021To039
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:37:21.377281+00:00
-- url     : https://prove2.me/submissions/80dfb403-9f33-4a0e-9255-bc4215fd86a0

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
theorem cell021_covered : CellCovered ⟨165,4544501,1495099⟩ ⟨170,4486691,1492638⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨165,4544501,1495099⟩ ⟨170,4486691,1492638⟩ (33/200) (17/100) 0 (17/100) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (88069/128000) (rectSplit1 (17/200) (rectSplit2 (624143/1024000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (3763987/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (32122121/40960000) (rectSplit1 (17/800) (rectSplit2 (126478259/163840000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell022_covered : CellCovered ⟨170,4486691,1492638⟩ ⟨175,4438167,1489159⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨170,4486691,1492638⟩ ⟨175,4438167,1489159⟩ (17/100) (7/40) 0 (7/40) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (88069/128000) (rectSplit1 (7/80) (rectSplit2 (624143/1024000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (3763987/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (32122121/40960000) (rectSplit2 (254966743/327680000) (rectSplit2 (1997519219/2621440000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell023_covered : CellCovered ⟨175,4438167,1489159⟩ ⟨180,4387653,1486415⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨175,4438167,1489159⟩ ⟨180,4387653,1486415⟩ (7/40) (9/50) 0 (9/50) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (88069/128000) (rectSplit1 (9/80) (rectSplit2 (800281/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (3763987/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (16262083/20480000) (rectSplit1 (9/200) (rectSplit2 (126478259/163840000) (rectLeaf (by decide +kernel)) (rectSplit2 (256574923/327680000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell024_covered : CellCovered ⟨180,4387653,1486415⟩ ⟨185,4340365,1483547⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨180,4387653,1486415⟩ ⟨185,4340365,1483547⟩ (9/50) (37/200) 0 (37/200) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (88069/128000) (rectSplit1 (37/320) (rectSplit2 (800281/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (3763987/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (16262083/20480000) (rectSplit1 (37/800) (rectSplit2 (126478259/163840000) (rectLeaf (by decide +kernel)) (rectSplit2 (256574923/327680000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell025_covered : CellCovered ⟨185,4340365,1483547⟩ ⟨190,4300648,1479786⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨185,4340365,1483547⟩ ⟨190,4300648,1479786⟩ (37/200) (19/100) 0 (19/100) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (88069/128000) (rectSplit1 (19/160) (rectSplit2 (3281533/5120000) (rectSplit1 (57/1280) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (3763987/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (32122121/40960000) (rectSplit2 (250946293/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (2049785069/2621440000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell026_covered : CellCovered ⟨190,4300648,1479786⟩ ⟨195,4259196,1476646⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨190,4300648,1479786⟩ ⟨195,4259196,1476646⟩ (19/100) (39/200) 0 (39/200) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (88069/128000) (rectSplit1 (39/320) (rectSplit2 (3281533/5120000) (rectSplit1 (117/2560) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (3763987/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (16262083/20480000) (rectSplit1 (39/800) (rectSplit2 (126478259/163840000) (rectLeaf (by decide +kernel)) (rectSplit2 (256574923/327680000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell027_covered : CellCovered ⟨195,4259196,1476646⟩ ⟨200,4220329,1473382⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨195,4259196,1476646⟩ ⟨200,4220329,1473382⟩ (39/200) (1/5) 0 (1/5) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (1841789/2560000) (rectSplit1 (3/20) (rectSplit2 (6965111/10240000) (rectSplit1 (9/160) (rectSplit2 (52102483/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (8090837/10240000) (rectSplit1 (1/20) (rectSplit2 (62555653/81920000) (rectLeaf (by decide +kernel)) (rectSplit2 (256735741/327680000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell028_covered : CellCovered ⟨200,4220329,1473382⟩ ⟨205,4187680,1469330⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨200,4220329,1473382⟩ ⟨205,4187680,1469330⟩ (1/5) (41/200) 0 (41/200) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (1841789/2560000) (rectSplit1 (123/800) (rectSplit2 (6965111/10240000) (rectSplit1 (369/6400) (rectSplit2 (52102483/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (8090837/10240000) (rectSplit1 (41/800) (rectSplit2 (62555653/81920000) (rectLeaf (by decide +kernel)) (rectSplit2 (256735741/327680000) (rectSplit2 (2047372799/2621440000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell029_covered : CellCovered ⟨205,4187680,1469330⟩ ⟨210,4153572,1465798⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨205,4187680,1469330⟩ ⟨210,4153572,1465798⟩ (41/200) (21/100) 0 (21/100) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (1841789/2560000) (rectSplit1 (63/400) (rectSplit1 (63/640) (rectSplit2 (13528177/20480000) (rectSplit2 (102194741/163840000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (8090837/10240000) (rectSplit1 (21/400) (rectSplit2 (62555653/81920000) (rectLeaf (by decide +kernel)) (rectSplit2 (256735741/327680000) (rectSplit2 (2047372799/2621440000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell030_covered : CellCovered ⟨210,4153572,1465798⟩ ⟨215,4121594,1462144⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨210,4153572,1465798⟩ ⟨215,4121594,1462144⟩ (21/100) (43/200) 0 (43/200) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (961099/1280000) (rectSplit1 (301/1600) (rectSplit2 (1489513/2048000) (rectSplit1 (903/6400) (rectSplit2 (28101671/40960000) (rectSplit1 (2709/51200) (rectSplit2 (209616067/327680000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (8090837/10240000) (rectSplit1 (43/1600) (rectSplit2 (31961303/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (256896559/327680000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell031_covered : CellCovered ⟨215,4121594,1462144⟩ ⟨220,4094721,1457786⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨215,4121594,1462144⟩ ⟨220,4094721,1457786⟩ (43/200) (11/50) 0 (11/50) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (961099/1280000) (rectSplit1 (77/400) (rectSplit2 (1489513/2048000) (rectSplit1 (231/1600) (rectSplit2 (2045503/3276800) (rectLeaf (by decide +kernel)) (rectSplit1 (693/12800) (rectSplit2 (18052613/26214400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (8090837/10240000) (rectSplit1 (11/400) (rectSplit2 (31961303/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (256896559/327680000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell032_covered : CellCovered ⟨220,4094721,1457786⟩ ⟨225,4066452,1453810⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨220,4094721,1457786⟩ ⟨225,4066452,1453810⟩ (11/50) (9/40) 0 (9/40) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (961099/1280000) (rectSplit1 (63/320) (rectSplit1 (441/2560) (rectSplit2 (624143/1024000) (rectLeaf (by decide +kernel)) (rectSplit1 (441/4096) (rectSplit2 (6965111/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (8090837/10240000) (rectSplit1 (9/320) (rectSplit2 (31961303/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (256896559/327680000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell033_covered : CellCovered ⟨225,4066452,1453810⟩ ⟨230,4042304,1449194⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨225,4066452,1453810⟩ ⟨230,4042304,1449194⟩ (9/40) (23/100) 0 (23/100) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (961099/1280000) (rectSplit1 (161/800) (rectSplit1 (1127/6400) (rectSplit2 (624143/1024000) (rectLeaf (by decide +kernel)) (rectSplit1 (1127/10240) (rectSplit2 (6965111/10240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (69/800) (rectSplit2 (8090837/10240000) (rectSplit2 (63520561/81920000) (rectLeaf (by decide +kernel)) (rectSplit2 (514195163/655360000) (rectSplit2 (4107530629/5242880000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell034_covered : CellCovered ⟨230,4042304,1449194⟩ ⟨235,4017211,1444865⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨230,4042304,1449194⟩ ⟨235,4017211,1444865⟩ (23/100) (47/200) 0 (47/200) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (961099/1280000) (rectSplit1 (329/1600) (rectSplit1 (2303/12800) (rectSplit2 (624143/1024000) (rectLeaf (by decide +kernel)) (rectSplit1 (2303/20480) (rectSplit2 (228673/327680) (rectSplit1 (6909/163840) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (141/1600) (rectSplit2 (8090837/10240000) (rectSplit2 (31961303/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (256896559/327680000) (rectSplit2 (1023967831/1310720000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell035_covered : CellCovered ⟨235,4017211,1444865⟩ ⟨240,3995561,1439992⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨235,4017211,1444865⟩ ⟨240,3995561,1439992⟩ (47/200) (6/25) 0 (6/25) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (961099/1280000) (rectSplit1 (21/100) (rectSplit1 (147/800) (rectSplit2 (624143/1024000) (rectLeaf (by decide +kernel)) (rectSplit1 (147/1280) (rectSplit2 (228673/327680) (rectSplit1 (441/10240) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (9/100) (rectSplit2 (8090837/10240000) (rectSplit2 (31961303/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (256896559/327680000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell036_covered : CellCovered ⟨240,3995561,1439992⟩ ⟨245,3973376,1435319⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨240,3995561,1439992⟩ ⟨245,3973376,1435319⟩ (6/25) (49/200) 0 (49/200) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (961099/1280000) (rectSplit1 (343/1600) (rectSplit1 (2401/12800) (rectSplit2 (624143/1024000) (rectLeaf (by decide +kernel)) (rectSplit1 (2401/20480) (rectSplit2 (14653903/20480000) (rectSplit1 (7203/163840) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (147/1600) (rectSplit2 (4085623/5120000) (rectSplit2 (3220253/4096000) (rectSplit2 (63681379/81920000) (rectLeaf (by decide +kernel)) (rectSplit2 (256896559/327680000) (rectSplit1 (147/12800) (rectSplit2 (2053001429/2621440000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell037_covered : CellCovered ⟨245,3973376,1435319⟩ ⟨250,3952515,1430488⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨245,3973376,1435319⟩ ⟨250,3952515,1430488⟩ (49/200) (1/4) 0 (1/4) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (7/32) (rectSplit1 (49/256) (rectSplit2 (194737/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (245/2048) (rectSplit2 (911869/1280000) (rectSplit1 (735/16384) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (3/32) (rectSplit2 (253813/320000) (rectSplit2 (1986197/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (16111111/20480000) (rectSplit1 (3/256) (rectSplit2 (64222909/81920000) (rectSplit2 (513118667/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (1026901939/1310720000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (137573/160000) (rectSplit2 (1075969/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell038_covered : CellCovered ⟨250,3952515,1430488⟩ ⟨251,3950044,1429201⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨250,3952515,1430488⟩ ⟨251,3950044,1429201⟩ (1/4) (251/1000) 0 (251/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (1757/8000) (rectSplit1 (12299/64000) (rectSplit1 (36897/256000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (110691/2048000) (rectSplit2 (941407/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (753/8000) (rectSplit2 (253813/320000) (rectSplit2 (1000483/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (4016701/5120000) (rectSplit2 (32089301/40960000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (137573/160000) (rectSplit2 (1075969/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell039_covered : CellCovered ⟨251,3950044,1429201⟩ ⟨252,3946093,1428205⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨251,3950044,1429201⟩ ⟨252,3946093,1428205⟩ (251/1000) (63/250) 0 (63/250) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (441/2000) (rectSplit1 (3087/16000) (rectSplit1 (9261/64000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (27783/512000) (rectSplit2 (941407/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (189/2000) (rectSplit2 (253813/320000) (rectSplit2 (1000483/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (4016701/5120000) (rectSplit2 (32089301/40960000) (rectSplit1 (189/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (137573/160000) (rectSplit2 (1075969/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 21).take 19), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨165,4544501,1495099⟩,⟨170,4486691,1492638⟩),(⟨170,4486691,1492638⟩,⟨175,4438167,1489159⟩),(⟨175,4438167,1489159⟩,⟨180,4387653,1486415⟩),(⟨180,4387653,1486415⟩,⟨185,4340365,1483547⟩),(⟨185,4340365,1483547⟩,⟨190,4300648,1479786⟩),(⟨190,4300648,1479786⟩,⟨195,4259196,1476646⟩),(⟨195,4259196,1476646⟩,⟨200,4220329,1473382⟩),(⟨200,4220329,1473382⟩,⟨205,4187680,1469330⟩),(⟨205,4187680,1469330⟩,⟨210,4153572,1465798⟩),(⟨210,4153572,1465798⟩,⟨215,4121594,1462144⟩),(⟨215,4121594,1462144⟩,⟨220,4094721,1457786⟩),(⟨220,4094721,1457786⟩,⟨225,4066452,1453810⟩),(⟨225,4066452,1453810⟩,⟨230,4042304,1449194⟩),(⟨230,4042304,1449194⟩,⟨235,4017211,1444865⟩),(⟨235,4017211,1444865⟩,⟨240,3995561,1439992⟩),(⟨240,3995561,1439992⟩,⟨245,3973376,1435319⟩),(⟨245,3973376,1435319⟩,⟨250,3952515,1430488⟩),(⟨250,3952515,1430488⟩,⟨251,3950044,1429201⟩),(⟨251,3950044,1429201⟩,⟨252,3946093,1428205⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell021_covered ?_
  refine slabCons cell022_covered ?_
  refine slabCons cell023_covered ?_
  refine slabCons cell024_covered ?_
  refine slabCons cell025_covered ?_
  refine slabCons cell026_covered ?_
  refine slabCons cell027_covered ?_
  refine slabCons cell028_covered ?_
  refine slabCons cell029_covered ?_
  refine slabCons cell030_covered ?_
  refine slabCons cell031_covered ?_
  refine slabCons cell032_covered ?_
  refine slabCons cell033_covered ?_
  refine slabCons cell034_covered ?_
  refine slabCons cell035_covered ?_
  refine slabCons cell036_covered ?_
  refine slabCons cell037_covered ?_
  refine slabCons cell038_covered ?_
  refine slabCons cell039_covered ?_
  simp
