-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells071To081
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:37:29.528709+00:00
-- url     : https://prove2.me/submissions/3ae98a8a-3ecc-4c05-afb4-549172f16f01

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
theorem cell071_covered : CellCovered ⟨283,3847588,1394585⟩ ⟨284,3844903,1393548⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨283,3847588,1394585⟩ ⟨284,3844903,1393548⟩ (283/1000) (71/250) 0 (71/250) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (71/500) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (71/1000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (781/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (71/500) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2071529/2560000) (rectSplit2 (16498387/20480000) (rectSplit2 (128368691/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (71/4000) (rectSplit2 (517093169/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (2079227891/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (8414608499/10485760000) (rectSplit2 (66828383317/83886080000) (rectLeaf (by decide +kernel)) (rectSplit2 (134145251309/167772160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (213/2000) (rectSplit2 (138667/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (497/2000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell072_covered : CellCovered ⟨284,3844903,1393548⟩ ⟨285,3842247,1392508⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨284,3844903,1393548⟩ ⟨285,3842247,1392508⟩ (71/250) (57/200) 0 (57/200) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (57/400) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (57/800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (627/3200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (57/400) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2071529/2560000) (rectSplit2 (16055317/20480000) (rectLeaf (by decide +kernel)) (rectSplit1 (57/1600) (rectSplit2 (64738183/81920000) (rectLeaf (by decide +kernel)) (rectSplit2 (263604967/327680000) (rectSplit1 (57/12800) (rectSplit2 (2085578561/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (4194418297/5242880000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (171/1600) (rectSplit2 (138667/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (399/1600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell073_covered : CellCovered ⟨285,3842247,1392508⟩ ⟨286,3839620,1391463⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨285,3842247,1392508⟩ ⟨286,3839620,1391463⟩ (57/200) (143/500) 0 (143/500) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (143/1000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (143/2000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (1573/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (143/1000) (rectSplit1 (143/1600) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2071529/2560000) (rectSplit2 (16055317/20480000) (rectLeaf (by decide +kernel)) (rectSplit1 (143/6400) (rectSplit2 (64738183/81920000) (rectLeaf (by decide +kernel)) (rectSplit2 (260503477/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (1055970613/1310720000) (rectSplit1 (143/51200) (rectSplit2 (2097984521/2621440000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (143/1000) (rectSplit2 (138667/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (1001/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell074_covered : CellCovered ⟨286,3839620,1391463⟩ ⟨287,3837023,1390416⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨286,3839620,1391463⟩ ⟨287,3837023,1390416⟩ (143/500) (287/1000) 0 (287/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (287/2000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (287/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (3157/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (287/2000) (rectSplit1 (287/3200) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2071529/2560000) (rectSplit2 (16055317/20480000) (rectLeaf (by decide +kernel)) (rectSplit1 (287/12800) (rectSplit2 (64738183/81920000) (rectLeaf (by decide +kernel)) (rectSplit2 (260503477/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (1055970613/1310720000) (rectSplit1 (287/102400) (rectSplit2 (2097984521/2621440000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (287/2000) (rectSplit2 (138667/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (2009/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell075_covered : CellCovered ⟨287,3837023,1390416⟩ ⟨288,3834690,1389318⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨287,3837023,1390416⟩ ⟨288,3834690,1389318⟩ (287/1000) (36/125) 0 (36/125) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (18/125) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (9/125) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (99/500) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (18/125) (rectSplit1 (9/100) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2071529/2560000) (rectSplit2 (16055317/20480000) (rectLeaf (by decide +kernel)) (rectSplit1 (9/400) (rectSplit2 (64738183/81920000) (rectLeaf (by decide +kernel)) (rectSplit2 (260503477/327680000) (rectLeaf (by decide +kernel)) (rectSplit2 (1055970613/1310720000) (rectSplit1 (9/3200) (rectSplit2 (2097984521/2621440000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (18/125) (rectSplit2 (109949/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (904207/1024000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (63/250) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell076_covered : CellCovered ⟨288,3834690,1389318⟩ ⟨289,3832170,1388259⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨288,3834690,1389318⟩ ⟨289,3832170,1388259⟩ (36/125) (289/1000) 0 (289/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (289/2000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (289/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (3179/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (289/2000) (rectSplit1 (289/3200) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4167673/5120000) (rectSplit2 (33169079/40960000) (rectSplit2 (256909687/327680000) (rectLeaf (by decide +kernel)) (rectSplit1 (289/12800) (rectSplit2 (1036081693/1310720000) (rectLeaf (by decide +kernel)) (rectSplit2 (4169655607/5242880000) (rectLeaf (by decide +kernel)) (rectSplit2 (16906581943/20971520000) (rectSplit1 (289/102400) (rectSplit2 (33585204371/41943040000) (rectLeaf (by decide +kernel)) (rectSplit2 (67398368257/83886080000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (289/2000) (rectSplit2 (109949/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (904207/1024000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (2023/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell077_covered : CellCovered ⟨289,3832170,1388259⟩ ⟨290,3829678,1387197⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨289,3832170,1388259⟩ ⟨290,3829678,1387197⟩ (289/1000) (29/100) 0 (29/100) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (29/200) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (29/400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (319/1600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (29/200) (rectSplit1 (29/320) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4167673/5120000) (rectSplit2 (32135249/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (29/1280) (rectSplit2 (129747131/163840000) (rectLeaf (by decide +kernel)) (rectSplit2 (529843739/655360000) (rectSplit2 (2086809311/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (8444934179/10485760000) (rectSplit1 (29/10240) (rectSplit2 (16792171423/20971520000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (29/200) (rectSplit2 (109949/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (904207/1024000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (203/800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell078_covered : CellCovered ⟨290,3829678,1387197⟩ ⟨291,3827214,1386131⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨290,3829678,1387197⟩ ⟨291,3827214,1386131⟩ (29/100) (291/1000) 0 (291/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (291/2000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (291/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (3201/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (291/2000) (rectSplit1 (291/3200) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4167673/5120000) (rectSplit2 (32135249/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (291/12800) (rectSplit2 (129747131/163840000) (rectLeaf (by decide +kernel)) (rectSplit2 (522606929/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (2122993361/2621440000) (rectSplit1 (291/102400) (rectSplit2 (8459407799/10485760000) (rectSplit2 (16821118663/20971520000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (291/2000) (rectSplit2 (109949/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (224821/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (2037/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell079_covered : CellCovered ⟨291,3827214,1386131⟩ ⟨292,3824777,1385062⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨291,3827214,1386131⟩ ⟨292,3824777,1385062⟩ (291/1000) (73/250) 0 (73/250) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (73/500) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (73/1000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (803/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (73/500) (rectSplit1 (73/800) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4167673/5120000) (rectSplit2 (32135249/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (73/3200) (rectSplit2 (129747131/163840000) (rectLeaf (by decide +kernel)) (rectSplit2 (522606929/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (2122993361/2621440000) (rectSplit1 (73/25600) (rectSplit2 (16821118663/20971520000) (rectLeaf (by decide +kernel)) (rectSplit2 (33805065551/41943040000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (73/500) (rectSplit2 (109949/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (224821/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (511/2000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell080_covered : CellCovered ⟨292,3824777,1385062⟩ ⟨293,3822369,1383989⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨292,3824777,1385062⟩ ⟨293,3822369,1383989⟩ (73/250) (293/1000) 0 (293/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (293/2000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (293/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (3223/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (293/2000) (rectSplit1 (293/3200) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4167673/5120000) (rectSplit2 (32135249/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (293/12800) (rectSplit2 (129747131/163840000) (rectLeaf (by decide +kernel)) (rectSplit2 (522606929/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (2122993361/2621440000) (rectSplit1 (293/102400) (rectSplit2 (16821118663/20971520000) (rectLeaf (by decide +kernel)) (rectSplit2 (33805065551/41943040000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (293/2000) (rectSplit2 (109949/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (224821/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (2051/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell081_covered : CellCovered ⟨293,3822369,1383989⟩ ⟨294,3819987,1382913⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨293,3822369,1383989⟩ ⟨294,3819987,1382913⟩ (293/1000) (147/500) 0 (147/500) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (147/1000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (147/2000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (1617/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (147/1000) (rectSplit1 (147/1600) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4167673/5120000) (rectSplit2 (32135249/40960000) (rectLeaf (by decide +kernel)) (rectSplit1 (147/6400) (rectSplit2 (129747131/163840000) (rectLeaf (by decide +kernel)) (rectSplit2 (522606929/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (2122993361/2621440000) (rectSplit1 (147/51200) (rectSplit2 (16821118663/20971520000) (rectLeaf (by decide +kernel)) (rectSplit2 (135383090429/167772160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (147/1000) (rectSplit2 (109949/128000) (rectLeaf (by decide +kernel)) (rectSplit2 (224821/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectSplit1 (1029/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 71).take 11), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨283,3847588,1394585⟩,⟨284,3844903,1393548⟩),(⟨284,3844903,1393548⟩,⟨285,3842247,1392508⟩),(⟨285,3842247,1392508⟩,⟨286,3839620,1391463⟩),(⟨286,3839620,1391463⟩,⟨287,3837023,1390416⟩),(⟨287,3837023,1390416⟩,⟨288,3834690,1389318⟩),(⟨288,3834690,1389318⟩,⟨289,3832170,1388259⟩),(⟨289,3832170,1388259⟩,⟨290,3829678,1387197⟩),(⟨290,3829678,1387197⟩,⟨291,3827214,1386131⟩),(⟨291,3827214,1386131⟩,⟨292,3824777,1385062⟩),(⟨292,3824777,1385062⟩,⟨293,3822369,1383989⟩),(⟨293,3822369,1383989⟩,⟨294,3819987,1382913⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell071_covered ?_
  refine slabCons cell072_covered ?_
  refine slabCons cell073_covered ?_
  refine slabCons cell074_covered ?_
  refine slabCons cell075_covered ?_
  refine slabCons cell076_covered ?_
  refine slabCons cell077_covered ?_
  refine slabCons cell078_covered ?_
  refine slabCons cell079_covered ?_
  refine slabCons cell080_covered ?_
  refine slabCons cell081_covered ?_
  simp
