-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells094To103
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:38:55.762181+00:00
-- url     : https://prove2.me/submissions/18f37126-dbc3-423b-b85c-3a25f877c58b

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
theorem cell094_covered : CellCovered ⟨306,3794368,1370786⟩ ⟨307,3792470,1369757⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨306,3794368,1370786⟩ ⟨307,3792470,1369757⟩ (153/500) (307/1000) 0 (307/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (307/2000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (307/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (3377/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (307/2000) (rectSplit1 (307/3200) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (526771/640000) (rectSplit1 (921/25600) (rectSplit2 (2033239/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (8206801/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (33491809/40960000) (rectSplit1 (921/102400) (rectSplit2 (264611447/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (2133506701/2621440000) (rectSplit2 (17018208233/20971520000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (307/2000) (rectSplit2 (138667/160000) (rectSplit2 (1094567/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (2149/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell095_covered : CellCovered ⟨307,3792470,1369757⟩ ⟨308,3790607,1368723⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨307,3792470,1369757⟩ ⟨308,3790607,1368723⟩ (307/1000) (77/250) 0 (77/250) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (77/500) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (77/1000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (847/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (77/500) (rectSplit1 (77/800) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (526771/640000) (rectSplit1 (231/6400) (rectSplit2 (4189553/5120000) (rectSplit2 (32654899/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (263823767/327680000) (rectLeaf (by decide +kernel)) (rectSplit1 (231/51200) (rectSplit2 (2123513011/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (4268564147/5242880000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (77/500) (rectSplit2 (138667/160000) (rectSplit2 (1094567/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (539/2000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell096_covered : CellCovered ⟨308,3790607,1368723⟩ ⟨309,3788777,1367683⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨308,3790607,1368723⟩ ⟨309,3788777,1367683⟩ (77/250) (309/1000) 0 (309/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (309/2000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (309/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (3399/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (309/2000) (rectSplit1 (309/3200) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (526771/640000) (rectSplit1 (927/25600) (rectSplit2 (4189553/5120000) (rectSplit2 (32654899/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (263823767/327680000) (rectLeaf (by decide +kernel)) (rectSplit1 (927/204800) (rectSplit2 (2123513011/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (4268564147/5242880000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (309/2000) (rectSplit2 (138667/160000) (rectSplit2 (1094567/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (2163/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell097_covered : CellCovered ⟨309,3788777,1367683⟩ ⟨310,3786978,1366639⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨309,3788777,1367683⟩ ⟨310,3786978,1366639⟩ (309/1000) (31/100) 0 (31/100) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (31/200) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (31/400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (220993/320000) (rectSplit1 (403/1600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (31/200) (rectSplit1 (31/320) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (526771/640000) (rectSplit1 (93/2560) (rectSplit2 (4091093/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (16487447/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (67057463/81920000) (rectSplit1 (93/20480) (rectSplit2 (530921329/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (1067381033/1310720000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (31/200) (rectSplit2 (138667/160000) (rectSplit2 (272411/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (217/800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell098_covered : CellCovered ⟨310,3786978,1366639⟩ ⟨311,3785211,1365591⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨310,3786978,1366639⟩ ⟨311,3785211,1365591⟩ (31/100) (311/1000) 0 (311/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (311/2000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (311/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (220993/320000) (rectSplit1 (4043/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (311/2000) (rectSplit1 (311/3200) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (526771/640000) (rectSplit1 (933/25600) (rectSplit2 (4091093/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (16487447/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (67057463/81920000) (rectSplit1 (933/204800) (rectSplit2 (530921329/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (1067381033/1310720000) (rectLeaf (by decide +kernel)) (rectSplit2 (2140300441/2621440000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (311/2000) (rectSplit2 (138667/160000) (rectSplit2 (272411/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (2177/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell099_covered : CellCovered ⟨311,3785211,1365591⟩ ⟨312,3783475,1364538⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨311,3785211,1365591⟩ ⟨312,3783475,1364538⟩ (311/1000) (39/125) 0 (39/125) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (39/250) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (39/500) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (429/2000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (39/250) (rectSplit1 (39/400) (rectSplit1 (117/1600) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (510361/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2115289/2560000) (rectSplit1 (351/12800) (rectSplit2 (8239621/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (33623089/40960000) (rectSplit2 (132498541/163840000) (rectLeaf (by decide +kernel)) (rectSplit2 (535975609/655360000) (rectSplit1 (351/102400) (rectSplit2 (1065969773/1310720000) (rectLeaf (by decide +kernel)) (rectSplit2 (2137920991/2621440000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (39/250) (rectSplit2 (138667/160000) (rectSplit2 (272411/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (273/1000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell100_covered : CellCovered ⟨312,3783475,1364538⟩ ⟨313,3781771,1363480⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨312,3783475,1364538⟩ ⟨313,3781771,1363480⟩ (39/125) (313/1000) 0 (313/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (313/2000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (313/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (3443/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (313/2000) (rectSplit1 (313/3200) (rectSplit1 (939/12800) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (510361/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2115289/2560000) (rectSplit1 (2817/102400) (rectSplit2 (8239621/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (33623089/40960000) (rectSplit2 (132498541/163840000) (rectLeaf (by decide +kernel)) (rectSplit2 (535975609/655360000) (rectSplit2 (4257897647/5242880000) (rectLeaf (by decide +kernel)) (rectSplit1 (2817/819200) (rectSplit2 (8545702519/10485760000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (313/2000) (rectSplit2 (138667/160000) (rectSplit2 (272411/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (2191/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell101_covered : CellCovered ⟨313,3781771,1363480⟩ ⟨314,3780093,1362418⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨313,3781771,1363480⟩ ⟨314,3780093,1362418⟩ (313/1000) (157/500) 0 (157/500) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (157/1000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (157/2000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (1727/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (157/1000) (rectSplit1 (157/1600) (rectSplit1 (471/6400) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (510361/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2115289/2560000) (rectSplit1 (1413/51200) (rectSplit2 (8239621/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (33623089/40960000) (rectSplit2 (132498541/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (1413/409600) (rectSplit2 (1065969773/1310720000) (rectLeaf (by decide +kernel)) (rectSplit2 (2141908621/2621440000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (157/1000) (rectSplit2 (138667/160000) (rectSplit2 (272411/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (1099/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell102_covered : CellCovered ⟨314,3780093,1362418⟩ ⟨315,3778438,1361353⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨314,3780093,1362418⟩ ⟨315,3778438,1361353⟩ (157/500) (63/200) 0 (63/200) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (63/400) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (63/800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (693/3200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (63/400) (rectSplit1 (63/640) (rectSplit1 (441/5120) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (510361/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2115289/2560000) (rectSplit1 (441/20480) (rectSplit2 (8239621/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (33623089/40960000) (rectSplit2 (132498541/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (441/81920) (rectSplit2 (1065969773/1310720000) (rectLeaf (by decide +kernel)) (rectSplit2 (2141908621/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (17165176193/20971520000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (63/400) (rectSplit2 (138667/160000) (rectSplit2 (272411/320000) (rectSplit2 (434873/512000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (441/1600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell103_covered : CellCovered ⟨315,3778438,1361353⟩ ⟨316,3776815,1360283⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨315,3778438,1361353⟩ ⟨316,3776815,1360283⟩ (63/200) (79/250) 0 (79/250) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (79/500) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (79/1000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (869/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (79/500) (rectSplit1 (79/800) (rectSplit1 (553/6400) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (510361/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2115289/2560000) (rectSplit1 (553/25600) (rectSplit2 (8239621/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (33623089/40960000) (rectSplit2 (265661687/327680000) (rectLeaf (by decide +kernel)) (rectSplit1 (553/204800) (rectSplit2 (2135262571/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (4287140267/5242880000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (79/500) (rectSplit2 (138667/160000) (rectSplit2 (272411/320000) (rectSplit2 (434873/512000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (553/2000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 94).take 10), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨306,3794368,1370786⟩,⟨307,3792470,1369757⟩),(⟨307,3792470,1369757⟩,⟨308,3790607,1368723⟩),(⟨308,3790607,1368723⟩,⟨309,3788777,1367683⟩),(⟨309,3788777,1367683⟩,⟨310,3786978,1366639⟩),(⟨310,3786978,1366639⟩,⟨311,3785211,1365591⟩),(⟨311,3785211,1365591⟩,⟨312,3783475,1364538⟩),(⟨312,3783475,1364538⟩,⟨313,3781771,1363480⟩),(⟨313,3781771,1363480⟩,⟨314,3780093,1362418⟩),(⟨314,3780093,1362418⟩,⟨315,3778438,1361353⟩),(⟨315,3778438,1361353⟩,⟨316,3776815,1360283⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell094_covered ?_
  refine slabCons cell095_covered ?_
  refine slabCons cell096_covered ?_
  refine slabCons cell097_covered ?_
  refine slabCons cell098_covered ?_
  refine slabCons cell099_covered ?_
  refine slabCons cell100_covered ?_
  refine slabCons cell101_covered ?_
  refine slabCons cell102_covered ?_
  refine slabCons cell103_covered ?_
  simp
