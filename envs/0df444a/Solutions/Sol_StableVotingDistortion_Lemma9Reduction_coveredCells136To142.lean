-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells136To142
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:41:24.126681+00:00
-- url     : https://prove2.me/submissions/823d6633-e8df-482b-86b7-495f85205736

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
theorem cell136_covered : CellCovered ⟨348,3735404,1329987⟩ ⟨349,3733943,1329231⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨348,3735404,1329987⟩ ⟨349,3733943,1329231⟩ (87/250) (349/1000) 0 (349/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (349/1600) (rectSplit2 (9983/16000) (rectLeaf (by decide +kernel)) (rectSplit2 (414089/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit2 (28052441/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (2443/12800) (rectSplit2 (117275531/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (7329/51200) (rectSplit2 (983796151/1310720000) (rectLeaf (by decide +kernel)) (rectSplit1 (7329/81920) (rectSplit2 (2043578807/2621440000) (rectLeaf (by decide +kernel)) (rectSplit1 (7329/163840) (rectSplit2 (16728562981/20971520000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))))) (rectSplit2 (24889/32000) (rectSplit2 (214429/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (1047/4000) (rectSplit2 (137573/160000) (rectSplit1 (1047/8000) (rectSplit1 (1047/16000) (rectSplit2 (525677/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2127323/2560000) (rectLeaf (by decide +kernel)) (rectSplit1 (1047/64000) (rectSplit2 (8583137/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (34554083/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (138880937/163840000) (rectLeaf (by decide +kernel)) (rectSplit2 (557517563/655360000) (rectLeaf (by decide +kernel)) (rectSplit1 (1047/512000) (rectSplit2 (1121016571/1310720000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (1047/16000) (rectSplit2 (1105507/1280000) (rectSplit2 (883421/1024000) (rectSplit2 (35322071/40960000) (rectSplit1 (1047/128000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (349/2000) (rectLeaf (by decide +kernel)) (rectSplit2 (39453/40000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell137_covered : CellCovered ⟨349,3733943,1329231⟩ ⟨350,3732151,1328535⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨349,3733943,1329231⟩ ⟨350,3732151,1328535⟩ (349/1000) (7/20) 0 (7/20) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (7/32) (rectSplit2 (9983/16000) (rectLeaf (by decide +kernel)) (rectSplit2 (414089/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit2 (28052441/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (49/256) (rectSplit2 (117275531/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (147/1024) (rectSplit2 (983796151/1310720000) (rectLeaf (by decide +kernel)) (rectSplit1 (441/4096) (rectSplit2 (8098328723/10485760000) (rectLeaf (by decide +kernel)) (rectSplit1 (441/8192) (rectSplit2 (66686292409/83886080000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))))) (rectSplit2 (24889/32000) (rectSplit2 (214429/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (21/80) (rectSplit2 (137573/160000) (rectSplit1 (21/160) (rectSplit1 (21/320) (rectSplit2 (525677/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2127323/2560000) (rectLeaf (by decide +kernel)) (rectSplit1 (21/1280) (rectSplit2 (8583137/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (34554083/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (278426479/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (2237380907/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (4491376939/5242880000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (21/320) (rectSplit2 (1105507/1280000) (rectSplit2 (883421/1024000) (rectSplit1 (21/2560) (rectSplit2 (35322071/40960000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (7/32) (rectSplit1 (7/256) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell138_covered : CellCovered ⟨350,3732151,1328535⟩ ⟨351,3730392,1327921⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨350,3732151,1328535⟩ ⟨351,3730392,1327921⟩ (7/20) (351/1000) 0 (351/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (351/1600) (rectSplit2 (9983/16000) (rectLeaf (by decide +kernel)) (rectSplit2 (414089/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit2 (28052441/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (2457/12800) (rectSplit2 (117275531/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (7371/51200) (rectSplit2 (983796151/1310720000) (rectLeaf (by decide +kernel)) (rectSplit1 (22113/204800) (rectSplit2 (8098328723/10485760000) (rectLeaf (by decide +kernel)) (rectSplit1 (22113/409600) (rectSplit2 (66686292409/83886080000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))))) (rectSplit2 (24889/32000) (rectSplit2 (214429/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (1053/4000) (rectSplit2 (137573/160000) (rectSplit1 (1053/8000) (rectSplit1 (1053/16000) (rectSplit2 (525677/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2127323/2560000) (rectLeaf (by decide +kernel)) (rectSplit1 (1053/64000) (rectSplit2 (17240119/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (139028627/163840000) (rectLeaf (by decide +kernel)) (rectSplit2 (279903379/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (561652883/655360000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (1053/16000) (rectSplit2 (1105507/1280000) (rectSplit2 (883421/1024000) (rectSplit2 (17624113/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (70540759/81920000) (rectLeaf (by decide +kernel)) (rectSplit2 (112944967/131072000) (rectLeaf (by decide +kernel)) (rectSplit2 (904224341/1048576000) (rectLeaf (by decide +kernel)) (rectSplit1 (1053/128000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (351/1600) (rectSplit1 (351/12800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell139_covered : CellCovered ⟨351,3730392,1327921⟩ ⟨352,3728673,1327302⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨351,3730392,1327921⟩ ⟨352,3728673,1327302⟩ (351/1000) (44/125) 0 (44/125) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (11/50) (rectSplit2 (9983/16000) (rectLeaf (by decide +kernel)) (rectSplit2 (414089/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit2 (28052441/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (77/400) (rectSplit2 (117275531/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (231/1600) (rectSplit2 (983796151/1310720000) (rectLeaf (by decide +kernel)) (rectSplit1 (693/6400) (rectSplit2 (8098328723/10485760000) (rectLeaf (by decide +kernel)) (rectSplit1 (693/12800) (rectSplit2 (66686292409/83886080000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))))) (rectSplit2 (24889/32000) (rectSplit2 (214429/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (33/125) (rectSplit2 (137573/160000) (rectSplit1 (33/250) (rectSplit1 (33/500) (rectSplit2 (525677/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2127323/2560000) (rectLeaf (by decide +kernel)) (rectSplit1 (33/2000) (rectSplit2 (17240119/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (139028627/163840000) (rectLeaf (by decide +kernel)) (rectSplit2 (279903379/327680000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (33/500) (rectSplit2 (1105507/1280000) (rectSplit2 (883421/1024000) (rectSplit2 (35322071/40960000) (rectSplit1 (33/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (11/50) (rectSplit1 (11/400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell140_covered : CellCovered ⟨352,3728673,1327302⟩ ⟨353,3726994,1326678⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨352,3728673,1327302⟩ ⟨353,3726994,1326678⟩ (44/125) (353/1000) 0 (353/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (353/1600) (rectSplit2 (9983/16000) (rectLeaf (by decide +kernel)) (rectSplit2 (414089/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit2 (28052441/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (2471/12800) (rectSplit2 (117275531/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (7413/51200) (rectSplit2 (983796151/1310720000) (rectLeaf (by decide +kernel)) (rectSplit1 (22239/204800) (rectSplit2 (8098328723/10485760000) (rectLeaf (by decide +kernel)) (rectSplit1 (22239/409600) (rectSplit2 (66686292409/83886080000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))))) (rectSplit2 (24889/32000) (rectSplit2 (214429/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (1059/4000) (rectSplit2 (137573/160000) (rectSplit1 (1059/8000) (rectSplit1 (1059/16000) (rectSplit2 (525677/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2127323/2560000) (rectLeaf (by decide +kernel)) (rectSplit1 (1059/64000) (rectSplit2 (17240119/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (34849463/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (70068151/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (3177/32000) (rectSplit2 (1105507/1280000) (rectSplit2 (883421/1024000) (rectSplit2 (17624113/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (70540759/81920000) (rectLeaf (by decide +kernel)) (rectSplit2 (112944967/131072000) (rectLeaf (by decide +kernel)) (rectSplit2 (45204571/52428800) (rectLeaf (by decide +kernel)) (rectSplit2 (1808581603/2097152000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (353/1600) (rectSplit1 (353/12800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell141_covered : CellCovered ⟨353,3726994,1326678⟩ ⟨354,3725356,1326048⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨353,3726994,1326678⟩ ⟨354,3725356,1326048⟩ (353/1000) (177/500) 0 (177/500) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (177/800) (rectSplit2 (9983/16000) (rectLeaf (by decide +kernel)) (rectSplit2 (414089/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit2 (28052441/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (1239/6400) (rectSplit2 (117275531/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (3717/25600) (rectSplit2 (983796151/1310720000) (rectLeaf (by decide +kernel)) (rectSplit1 (11151/102400) (rectSplit2 (8098328723/10485760000) (rectLeaf (by decide +kernel)) (rectSplit1 (11151/204800) (rectSplit2 (66686292409/83886080000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))))) (rectSplit2 (24889/32000) (rectSplit2 (214429/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (531/2000) (rectSplit2 (137573/160000) (rectSplit1 (531/4000) (rectSplit1 (531/8000) (rectSplit2 (525677/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4279261/5120000) (rectLeaf (by decide +kernel)) (rectSplit1 (531/32000) (rectSplit2 (34603313/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (69822001/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (1593/16000) (rectSplit2 (1105507/1280000) (rectSplit2 (883421/1024000) (rectSplit2 (35322071/40960000) (rectSplit1 (1593/128000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (177/800) (rectSplit1 (177/6400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

theorem cell142_covered : CellCovered ⟨354,3725356,1326048⟩ ⟨355,3723757,1325414⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨354,3725356,1326048⟩ ⟨355,3723757,1325414⟩ (177/500) (71/200) 0 (71/200) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit1 (71/320) (rectSplit2 (9983/16000) (rectLeaf (by decide +kernel)) (rectSplit2 (414089/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (683219/1024000) (rectLeaf (by decide +kernel)) (rectSplit1 (213/2560) (rectSplit2 (15835423/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (128854427/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (639/20480) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit2 (7555871/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (781/5120) (rectSplit2 (64065373/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))))) (rectSplit2 (24889/32000) (rectSplit2 (214429/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (923/3200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (213/800) (rectSplit2 (137573/160000) (rectSplit1 (213/1600) (rectSplit1 (213/3200) (rectSplit2 (525677/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4279261/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (34603313/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (213/25600) (rectSplit2 (69822001/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (639/6400) (rectSplit2 (1105507/1280000) (rectSplit2 (883421/1024000) (rectSplit2 (35322071/40960000) (rectSplit1 (639/51200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (71/320) (rectSplit1 (71/2560) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 136).take 7), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨348,3735404,1329987⟩,⟨349,3733943,1329231⟩),(⟨349,3733943,1329231⟩,⟨350,3732151,1328535⟩),(⟨350,3732151,1328535⟩,⟨351,3730392,1327921⟩),(⟨351,3730392,1327921⟩,⟨352,3728673,1327302⟩),(⟨352,3728673,1327302⟩,⟨353,3726994,1326678⟩),(⟨353,3726994,1326678⟩,⟨354,3725356,1326048⟩),(⟨354,3725356,1326048⟩,⟨355,3723757,1325414⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell136_covered ?_
  refine slabCons cell137_covered ?_
  refine slabCons cell138_covered ?_
  refine slabCons cell139_covered ?_
  refine slabCons cell140_covered ?_
  refine slabCons cell141_covered ?_
  refine slabCons cell142_covered ?_
  simp
