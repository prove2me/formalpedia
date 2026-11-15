-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells000To020
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:37:19.452683+00:00
-- url     : https://prove2.me/submissions/d88f66a9-f047-4975-baf4-a50e7fd5d143

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
theorem cell000_covered : CellCovered ⟨60,8691175,1513624⟩ ⟨65,8109971,1518036⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨60,8691175,1513624⟩ ⟨65,8109971,1518036⟩ (3/50) (13/200) 0 (13/200) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (493951/640000) (rectSplit2 (853887/1280000) (rectSplit1 (39/1600) (rectSplit2 (6429051/10240000) (rectSplit2 (12188027/20480000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (39/1600) (rectSplit2 (3817593/5120000) (rectSplit2 (29334609/40960000) (rectSplit2 (56658993/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (2217031/2560000) (rectSplit2 (838567/1024000) (rectSplit2 (6467309/8192000) (rectSplit1 (13/1600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell001_covered : CellCovered ⟨65,8109971,1518036⟩ ⟨70,7617093,1521994⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨65,8109971,1518036⟩ ⟨70,7617093,1521994⟩ (13/200) (7/100) 0 (7/100) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (493951/640000) (rectSplit2 (853887/1280000) (rectSplit1 (21/800) (rectSplit2 (6429051/10240000) (rectSplit2 (12188027/20480000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (21/800) (rectSplit2 (7233141/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (15136357/20480000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit2 (2217031/2560000) (rectSplit2 (838567/1024000) (rectSplit2 (16047659/20480000) (rectSplit1 (7/800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell002_covered : CellCovered ⟨70,7617093,1521994⟩ ⟨75,7191413,1525860⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨70,7617093,1521994⟩ ⟨75,7191413,1525860⟩ (7/100) (3/40) 0 (3/40) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (493951/640000) (rectSplit2 (3013503/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (25046129/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (206935767/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (1701453281/2621440000) (rectLeaf (by decide +kernel)) (rectSplit1 (3/80) (rectSplit2 (7771123169/10485760000) (rectSplit2 (59273055217/83886080000) (rectSplit2 (113719560209/167772160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))))) (rectSplit2 (2217031/2560000) (rectSplit2 (838567/1024000) (rectSplit2 (16047659/20480000) (rectSplit1 (3/320) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell003_covered : CellCovered ⟨75,7191413,1525860⟩ ⟨80,6818918,1529781⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨75,7191413,1525860⟩ ⟨80,6818918,1529781⟩ (3/40) (2/25) 0 (2/25) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (493951/640000) (rectSplit2 (3013503/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (25046129/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (246336177/327680000) (rectSplit2 (1924722271/2621440000) (rectSplit2 (6733579039/10485760000) (rectLeaf (by decide +kernel)) (rectSplit1 (3/100) (rectSplit2 (14432468123/20971520000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectSplit2 (2217031/2560000) (rectSplit2 (838567/1024000) (rectSplit2 (16047659/20480000) (rectSplit1 (1/100) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell004_covered : CellCovered ⟨80,6818918,1529781⟩ ⟨85,6512066,1531365⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨80,6818918,1529781⟩ ⟨85,6512066,1531365⟩ (2/25) (17/200) 0 (17/200) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (547557/640000) (rectSplit2 (838567/1024000) (rectSplit2 (32229333/40960000) (rectSplit2 (193480661/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (1612199291/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (13348072349/20971520000) (rectLeaf (by decide +kernel)) (rectSplit2 (109937924939/167772160000) (rectLeaf (by decide +kernel)) (rectSplit2 (901576822541/1342177280000) (rectLeaf (by decide +kernel)) (rectSplit2 (3760821251367/5368709120000) (rectLeaf (by decide +kernel)) (rectSplit2 (33331363196199/42949672960000) (rectSplit1 (17/800) (rectSplit2 (12683586641427/17179869184000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell005_covered : CellCovered ⟨85,6512066,1531365⟩ ⟨90,6270015,1529575⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨85,6512066,1531365⟩ ⟨90,6270015,1529575⟩ (17/200) (9/100) 0 (9/100) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (547557/640000) (rectSplit2 (838567/1024000) (rectSplit2 (32229333/40960000) (rectSplit2 (193480661/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (1612199291/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (13348072349/20971520000) (rectLeaf (by decide +kernel)) (rectSplit2 (109937924939/167772160000) (rectLeaf (by decide +kernel)) (rectSplit2 (92365024557/134217728000) (rectLeaf (by decide +kernel)) (rectSplit2 (4158142865889/5368709120000) (rectSplit1 (9/400) (rectSplit2 (7852743848169/10737418240000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell006_covered : CellCovered ⟨90,6270015,1529575⟩ ⟨95,6068674,1526210⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨90,6270015,1529575⟩ ⟨95,6068674,1526210⟩ (9/100) (19/200) 0 (19/200) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (547557/640000) (rectSplit2 (838567/1024000) (rectSplit2 (32229333/40960000) (rectSplit2 (193480661/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (1612199291/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (642037619/838860800) (rectSplit2 (54743723459/83886080000) (rectLeaf (by decide +kernel)) (rectSplit1 (57/1600) (rectSplit2 (118947485359/167772160000) (rectLeaf (by decide +kernel)) (rectSplit2 (247355009159/335544320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell007_covered : CellCovered ⟨95,6068674,1526210⟩ ⟨100,5876716,1524428⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨95,6068674,1526210⟩ ⟨100,5876716,1524428⟩ (19/200) (1/10) 0 (1/10) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (547557/640000) (rectSplit2 (838567/1024000) (rectSplit2 (32229333/40960000) (rectSplit2 (193480661/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (1612199291/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (1379855037/2097152000) (rectLeaf (by decide +kernel)) (rectSplit2 (28948534803/41943040000) (rectLeaf (by decide +kernel)) (rectSplit2 (259968393747/335544320000) (rectSplit1 (1/40) (rectSplit2 (491556672171/671088640000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell008_covered : CellCovered ⟨100,5876716,1524428⟩ ⟨105,5704620,1522657⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨100,5876716,1524428⟩ ⟨105,5704620,1522657⟩ (1/10) (21/200) 0 (21/200) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (547557/640000) (rectSplit2 (838567/1024000) (rectSplit2 (32229333/40960000) (rectSplit2 (193480661/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (838276647/1310720000) (rectLeaf (by decide +kernel)) (rectSplit2 (3546168597/5242880000) (rectLeaf (by decide +kernel)) (rectSplit2 (6484730193/8388608000) (rectSplit1 (21/800) (rectSplit2 (60792999741/83886080000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell009_covered : CellCovered ⟨105,5704620,1522657⟩ ⟨110,5549683,1520892⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨105,5704620,1522657⟩ ⟨110,5549683,1520892⟩ (21/200) (11/100) 0 (11/100) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (547557/640000) (rectSplit2 (838567/1024000) (rectSplit2 (32229333/40960000) (rectSplit2 (20267409/32768000) (rectLeaf (by decide +kernel)) (rectSplit2 (432928467/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (1814454729/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (16253195913/20971520000) (rectSplit1 (11/400) (rectSplit2 (6153766749/8388608000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell010_covered : CellCovered ⟨110,5549683,1520892⟩ ⟨115,5411158,1518930⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨110,5549683,1520892⟩ ⟨115,5411158,1518930⟩ (11/100) (23/200) 0 (23/200) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (547557/640000) (rectSplit2 (838567/1024000) (rectSplit2 (32229333/40960000) (rectSplit2 (20267409/32768000) (rectLeaf (by decide +kernel)) (rectSplit2 (432928467/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (4042613763/5242880000) (rectSplit2 (29444979969/41943040000) (rectLeaf (by decide +kernel)) (rectSplit1 (23/1600) (rectSplit2 (250039490427/335544320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell011_covered : CellCovered ⟨115,5411158,1518930⟩ ⟨120,5292922,1515962⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨115,5411158,1518930⟩ ⟨120,5292922,1515962⟩ (23/200) (3/25) 0 (3/25) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (547557/640000) (rectSplit2 (838567/1024000) (rectSplit2 (12831299/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (55265237/81920000) (rectLeaf (by decide +kernel)) (rectSplit2 (232881071/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (1037905391/1310720000) (rectSplit2 (8196862021/10485760000) (rectSplit1 (3/200) (rectSplit2 (63340892921/83886080000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell012_covered : CellCovered ⟨120,5292922,1515962⟩ ⟨125,5177377,1514164⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨120,5292922,1515962⟩ ⟨125,5177377,1514164⟩ (3/25) (1/8) 0 (1/8) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (547557/640000) (rectSplit2 (838567/1024000) (rectSplit2 (12831299/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (55265237/81920000) (rectLeaf (by decide +kernel)) (rectSplit2 (232881071/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (1037905391/1310720000) (rectSplit2 (8196862021/10485760000) (rectSplit1 (1/64) (rectSplit2 (63340892921/83886080000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell013_covered : CellCovered ⟨125,5177377,1514164⟩ ⟨130,5071995,1512355⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨125,5177377,1514164⟩ ⟨130,5071995,1512355⟩ (1/8) (13/100) 0 (13/100) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (547557/640000) (rectSplit2 (838567/1024000) (rectSplit2 (12831299/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (55265237/81920000) (rectLeaf (by decide +kernel)) (rectSplit2 (232881071/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (1037905391/1310720000) (rectSplit2 (8196862021/10485760000) (rectSplit1 (13/800) (rectSplit2 (63340892921/83886080000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell014_covered : CellCovered ⟨130,5071995,1512355⟩ ⟨135,4975646,1510528⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨130,5071995,1512355⟩ ⟨135,4975646,1510528⟩ (13/100) (27/200) 0 (27/200) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (547557/640000) (rectSplit2 (325473/512000) (rectLeaf (by decide +kernel)) (rectSplit2 (8198049/10240000) (rectSplit2 (27726429/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (115971483/163840000) (rectLeaf (by decide +kernel)) (rectSplit2 (973363767/1310720000) (rectLeaf (by decide +kernel)) (rectSplit1 (27/800) (rectSplit2 (8166842661/10485760000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell015_covered : CellCovered ⟨135,4975646,1510528⟩ ⟨140,4895419,1507429⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨135,4975646,1510528⟩ ⟨140,4895419,1507429⟩ (27/200) (7/50) 0 (7/50) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (547557/640000) (rectSplit2 (838567/1024000) (rectSplit2 (32229333/40960000) (rectSplit2 (55265237/81920000) (rectSplit1 (21/400) (rectSplit2 (414541609/655360000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (506475899/655360000) (rectSplit2 (3730037177/5242880000) (rectLeaf (by decide +kernel)) (rectSplit1 (7/400) (rectSplit2 (31449147491/41943040000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell016_covered : CellCovered ⟨140,4895419,1507429⟩ ⟨145,4813401,1505368⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨140,4895419,1507429⟩ ⟨145,4813401,1505368⟩ (7/50) (29/200) 0 (29/200) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (547557/640000) (rectSplit2 (838567/1024000) (rectSplit2 (32229333/40960000) (rectSplit2 (55265237/81920000) (rectSplit1 (87/1600) (rectSplit2 (414541609/655360000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (469702183/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (4079387479/5242880000) (rectSplit1 (29/1600) (rectSplit2 (31669789787/41943040000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell017_covered : CellCovered ⟨145,4813401,1505368⟩ ⟨150,4737080,1503128⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨145,4813401,1505368⟩ ⟨150,4737080,1503128⟩ (29/200) (3/20) 0 (3/20) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (547557/640000) (rectSplit2 (838567/1024000) (rectSplit2 (32229333/40960000) (rectSplit2 (55265237/81920000) (rectSplit1 (9/160) (rectSplit2 (414541609/655360000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (469702183/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (4079387479/5242880000) (rectSplit1 (3/160) (rectSplit2 (31669789787/41943040000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell018_covered : CellCovered ⟨150,4737080,1503128⟩ ⟨155,4670048,1500075⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨150,4737080,1503128⟩ ⟨155,4670048,1500075⟩ (3/20) (31/200) 0 (31/200) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (547557/640000) (rectSplit2 (838567/1024000) (rectSplit2 (32229333/40960000) (rectSplit2 (55265237/81920000) (rectSplit1 (93/1600) (rectSplit2 (414541609/655360000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (469702183/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (4079387479/5242880000) (rectSplit1 (31/1600) (rectSplit2 (31669789787/41943040000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell019_covered : CellCovered ⟨155,4670048,1500075⟩ ⟨160,4606370,1497421⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨155,4670048,1500075⟩ ⟨160,4606370,1497421⟩ (31/200) (4/25) 0 (4/25) (703/1250) 1 from
    (rectSplit2 (9453/10000) (rectSplit2 (14359/16000) (rectSplit2 (547557/640000) (rectSplit2 (838567/1024000) (rectSplit2 (32229333/40960000) (rectSplit2 (55265237/81920000) (rectSplit1 (2/25) (rectSplit2 (414541609/655360000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (469702183/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (4079387479/5242880000) (rectSplit1 (1/50) (rectSplit2 (31669789787/41943040000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell020_covered : CellCovered ⟨160,4606370,1497421⟩ ⟨165,4544501,1495099⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨160,4606370,1497421⟩ ⟨165,4544501,1495099⟩ (4/25) (33/200) 0 (33/200) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (33983/40000) (rectSplit2 (260377/320000) (rectSplit2 (88069/128000) (rectSplit1 (99/1600) (rectSplit2 (3281533/5120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit2 (3763987/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (32122121/40960000) (rectSplit1 (33/1600) (rectSplit2 (126478259/163840000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 0).take 21), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨60,8691175,1513624⟩,⟨65,8109971,1518036⟩),(⟨65,8109971,1518036⟩,⟨70,7617093,1521994⟩),(⟨70,7617093,1521994⟩,⟨75,7191413,1525860⟩),(⟨75,7191413,1525860⟩,⟨80,6818918,1529781⟩),(⟨80,6818918,1529781⟩,⟨85,6512066,1531365⟩),(⟨85,6512066,1531365⟩,⟨90,6270015,1529575⟩),(⟨90,6270015,1529575⟩,⟨95,6068674,1526210⟩),(⟨95,6068674,1526210⟩,⟨100,5876716,1524428⟩),(⟨100,5876716,1524428⟩,⟨105,5704620,1522657⟩),(⟨105,5704620,1522657⟩,⟨110,5549683,1520892⟩),(⟨110,5549683,1520892⟩,⟨115,5411158,1518930⟩),(⟨115,5411158,1518930⟩,⟨120,5292922,1515962⟩),(⟨120,5292922,1515962⟩,⟨125,5177377,1514164⟩),(⟨125,5177377,1514164⟩,⟨130,5071995,1512355⟩),(⟨130,5071995,1512355⟩,⟨135,4975646,1510528⟩),(⟨135,4975646,1510528⟩,⟨140,4895419,1507429⟩),(⟨140,4895419,1507429⟩,⟨145,4813401,1505368⟩),(⟨145,4813401,1505368⟩,⟨150,4737080,1503128⟩),(⟨150,4737080,1503128⟩,⟨155,4670048,1500075⟩),(⟨155,4670048,1500075⟩,⟨160,4606370,1497421⟩),(⟨160,4606370,1497421⟩,⟨165,4544501,1495099⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell000_covered ?_
  refine slabCons cell001_covered ?_
  refine slabCons cell002_covered ?_
  refine slabCons cell003_covered ?_
  refine slabCons cell004_covered ?_
  refine slabCons cell005_covered ?_
  refine slabCons cell006_covered ?_
  refine slabCons cell007_covered ?_
  refine slabCons cell008_covered ?_
  refine slabCons cell009_covered ?_
  refine slabCons cell010_covered ?_
  refine slabCons cell011_covered ?_
  refine slabCons cell012_covered ?_
  refine slabCons cell013_covered ?_
  refine slabCons cell014_covered ?_
  refine slabCons cell015_covered ?_
  refine slabCons cell016_covered ?_
  refine slabCons cell017_covered ?_
  refine slabCons cell018_covered ?_
  refine slabCons cell019_covered ?_
  refine slabCons cell020_covered ?_
  simp
