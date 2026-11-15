-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells082To091
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:37:31.465857+00:00
-- url     : https://prove2.me/submissions/3e8628a5-add7-4a9a-8abd-9786035d91d3

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
theorem cell082_covered : CellCovered ⟨294,3819987,1382913⟩ ⟨295,3817634,1381833⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨294,3819987,1382913⟩ ⟨295,3817634,1381833⟩ (147/500) (59/200) 0 (59/200) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (59/400) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (59/800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (649/3200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (59/400) (rectSplit1 (59/640) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4019983/5120000) (rectLeaf (by decide +kernel)) (rectSplit1 (177/5120) (rectSplit2 (16252237/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (66559693/81920000) (rectSplit1 (177/20480) (rectSplit2 (261586537/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (1050998383/1310720000) (rectLeaf (by decide +kernel)) (rectSplit2 (8449857179/10485760000) (rectLeaf (by decide +kernel)) (rectSplit2 (16969497883/20971520000) (rectSplit2 (33869212241/41943040000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (59/400) (rectSplit2 (109949/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (224821/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (413/1600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell083_covered : CellCovered ⟨295,3817634,1381833⟩ ⟨296,3815332,1380789⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨295,3817634,1381833⟩ ⟨296,3815332,1380789⟩ (59/200) (37/125) 0 (37/125) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (37/250) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (37/500) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (407/2000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (37/250) (rectSplit1 (37/400) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4019983/5120000) (rectLeaf (by decide +kernel)) (rectSplit1 (111/3200) (rectSplit2 (16252237/20480000) (rectLeaf (by decide +kernel)) (rectSplit2 (66559693/81920000) (rectSplit1 (111/12800) (rectSplit2 (261586537/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (1050998383/1310720000) (rectLeaf (by decide +kernel)) (rectSplit2 (8449857179/10485760000) (rectLeaf (by decide +kernel)) (rectSplit2 (16969497883/20971520000) (rectSplit2 (33869212241/41943040000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (37/250) (rectSplit2 (109949/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (224821/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (259/1000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell084_covered : CellCovered ⟨296,3815332,1380789⟩ ⟨297,3813072,1379812⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨296,3815332,1380789⟩ ⟨297,3813072,1379812⟩ (37/125) (297/1000) 0 (297/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (297/2000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (297/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (3267/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (297/2000) (rectSplit1 (297/3200) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (526771/640000) (rectSplit1 (891/25600) (rectSplit2 (2033239/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (8354491/10240000) (rectSplit2 (32753359/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (133007251/163840000) (rectSplit1 (891/204800) (rectSplit2 (1054088933/1310720000) (rectLeaf (by decide +kernel)) (rectSplit2 (2118146941/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (16975082753/20971520000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (297/2000) (rectSplit2 (109949/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (224821/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (2079/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell085_covered : CellCovered ⟨297,3813072,1379812⟩ ⟨298,3810849,1378830⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨297,3813072,1379812⟩ ⟨298,3810849,1378830⟩ (297/1000) (149/500) 0 (149/500) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (149/1000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (149/2000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (1639/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (149/1000) (rectSplit1 (149/1600) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (526771/640000) (rectSplit1 (447/12800) (rectSplit2 (2033239/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (8354491/10240000) (rectSplit2 (32753359/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (133007251/163840000) (rectSplit1 (447/102400) (rectSplit2 (1054088933/1310720000) (rectLeaf (by decide +kernel)) (rectSplit2 (8482556839/10485760000) (rectSplit2 (16915268303/20971520000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (149/1000) (rectSplit2 (109949/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (224821/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (1043/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell086_covered : CellCovered ⟨298,3810849,1378830⟩ ⟨299,3808662,1377843⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨298,3810849,1378830⟩ ⟨299,3808662,1377843⟩ (149/500) (299/1000) 0 (299/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (299/2000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (299/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (3289/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (299/2000) (rectSplit1 (299/3200) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (526771/640000) (rectSplit1 (897/25600) (rectSplit2 (2033239/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (8354491/10240000) (rectSplit1 (897/102400) (rectSplit2 (32753359/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (133007251/163840000) (rectSplit2 (1054088933/1310720000) (rectLeaf (by decide +kernel)) (rectSplit2 (8482556839/10485760000) (rectSplit2 (67710918587/83886080000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (299/2000) (rectSplit2 (109949/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (224821/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (2093/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell087_covered : CellCovered ⟨299,3808662,1377843⟩ ⟨300,3806511,1376850⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨299,3808662,1377843⟩ ⟨300,3806511,1376850⟩ (299/1000) (3/10) 0 (3/10) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (3/20) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (3/40) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (33/160) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (3/20) (rectSplit1 (3/32) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (526771/640000) (rectSplit1 (9/256) (rectSplit2 (2033239/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (8354491/10240000) (rectSplit1 (9/1024) (rectSplit2 (32753359/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (133007251/163840000) (rectSplit2 (1054088933/1310720000) (rectLeaf (by decide +kernel)) (rectSplit2 (8482556839/10485760000) (rectSplit2 (67710918587/83886080000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (3/20) (rectSplit2 (109949/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (224821/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (21/80) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell088_covered : CellCovered ⟨300,3806511,1376850⟩ ⟨301,3804397,1375853⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨300,3806511,1376850⟩ ⟨301,3804397,1375853⟩ (3/10) (301/1000) 0 (301/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (301/2000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (301/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (3311/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (301/2000) (rectSplit1 (301/3200) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (526771/640000) (rectSplit1 (903/25600) (rectSplit2 (2033239/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (8354491/10240000) (rectSplit1 (903/102400) (rectSplit2 (32753359/40960000) (rectLeaf (by decide +kernel)) (rectSplit2 (133007251/163840000) (rectSplit2 (1054088933/1310720000) (rectLeaf (by decide +kernel)) (rectSplit2 (8482556839/10485760000) (rectSplit2 (67710918587/83886080000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (301/2000) (rectSplit2 (109949/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (224821/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (2107/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell089_covered : CellCovered ⟨301,3804397,1375853⟩ ⟨302,3802319,1374850⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨301,3804397,1375853⟩ ⟨302,3802319,1374850⟩ (301/1000) (151/500) 0 (151/500) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (151/1000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (151/2000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (1661/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (151/1000) (rectSplit1 (151/1600) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (526771/640000) (rectSplit1 (453/12800) (rectSplit2 (2033239/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (8354491/10240000) (rectSplit2 (32753359/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (453/51200) (rectSplit2 (264020687/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (2128780621/2621440000) (rectSplit2 (16980399593/20971520000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (151/1000) (rectSplit2 (109949/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (224821/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (1057/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell090_covered : CellCovered ⟨302,3802319,1374850⟩ ⟨303,3800277,1373842⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨302,3802319,1374850⟩ ⟨303,3800277,1373842⟩ (151/500) (303/1000) 0 (303/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (303/2000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (303/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (3333/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (303/2000) (rectSplit1 (303/3200) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (526771/640000) (rectSplit1 (909/25600) (rectSplit2 (2033239/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (8354491/10240000) (rectSplit2 (65728253/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (909/204800) (rectSplit2 (529149049/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (1063836473/1310720000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (303/2000) (rectSplit2 (109949/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (224821/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (2121/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell091_covered : CellCovered ⟨303,3800277,1373842⟩ ⟨304,3798271,1372829⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨303,3800277,1373842⟩ ⟨304,3798271,1372829⟩ (303/1000) (38/125) 0 (38/125) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (19/125) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (19/250) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (209/1000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (19/125) (rectSplit1 (19/200) (rectSplit2 (125539/160000) (rectLeaf (by decide +kernel)) (rectSplit2 (526771/640000) (rectSplit1 (57/1600) (rectSplit2 (2033239/2560000) (rectLeaf (by decide +kernel)) (rectSplit2 (8206801/10240000) (rectLeaf (by decide +kernel)) (rectSplit2 (33491809/40960000) (rectSplit2 (133302631/163840000) (rectSplit1 (57/12800) (rectSplit2 (1056451973/1310720000) (rectLeaf (by decide +kernel)) (rectSplit2 (2122873021/2621440000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (19/125) (rectSplit2 (138667/160000) (rectSplit2 (1094567/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (133/500) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 82).take 10), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨294,3819987,1382913⟩,⟨295,3817634,1381833⟩),(⟨295,3817634,1381833⟩,⟨296,3815332,1380789⟩),(⟨296,3815332,1380789⟩,⟨297,3813072,1379812⟩),(⟨297,3813072,1379812⟩,⟨298,3810849,1378830⟩),(⟨298,3810849,1378830⟩,⟨299,3808662,1377843⟩),(⟨299,3808662,1377843⟩,⟨300,3806511,1376850⟩),(⟨300,3806511,1376850⟩,⟨301,3804397,1375853⟩),(⟨301,3804397,1375853⟩,⟨302,3802319,1374850⟩),(⟨302,3802319,1374850⟩,⟨303,3800277,1373842⟩),(⟨303,3800277,1373842⟩,⟨304,3798271,1372829⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell082_covered ?_
  refine slabCons cell083_covered ?_
  refine slabCons cell084_covered ?_
  refine slabCons cell085_covered ?_
  refine slabCons cell086_covered ?_
  refine slabCons cell087_covered ?_
  refine slabCons cell088_covered ?_
  refine slabCons cell089_covered ?_
  refine slabCons cell090_covered ?_
  refine slabCons cell091_covered ?_
  simp
