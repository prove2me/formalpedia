-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells060To070
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:37:27.585143+00:00
-- url     : https://prove2.me/submissions/335a2fb1-7321-40fd-89c1-b18e9778aeac

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
theorem cell060_covered : CellCovered ⟨272,3878795,1406641⟩ ⟨273,3875751,1405529⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨272,3878795,1406641⟩ ⟨273,3875751,1405529⟩ (34/125) (273/1000) 0 (273/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (819/8000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit2 (466601/640000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (204583/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (10647/64000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (819/8000) (rectSplit2 (131009/160000) (rectSplit2 (515831/640000) (rectSplit2 (4003573/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (16383517/20480000) (rectSplit2 (65164843/81920000) (rectSplit2 (520211069/655360000) (rectSplit2 (4153934827/5242880000) (rectSplit2 (32851546091/41943040000) (rectLeaf (by decide +kernel)) (rectSplit1 (819/64000) (rectSplit2 (263192301253/335544320000) (rectLeaf (by decide +kernel)) (rectSplit2 (529044130181/671088640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4240331624473/5368709120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (819/8000) (rectSplit2 (138667/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (1911/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell061_covered : CellCovered ⟨273,3875751,1405529⟩ ⟨274,3872738,1404412⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨273,3875751,1405529⟩ ⟨274,3872738,1404412⟩ (273/1000) (137/500) 0 (137/500) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (411/4000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit2 (466601/640000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (204583/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (5343/32000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (411/4000) (rectSplit2 (131009/160000) (rectSplit2 (515831/640000) (rectSplit2 (4003573/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (16383517/20480000) (rectSplit2 (65164843/81920000) (rectSplit2 (520211069/655360000) (rectSplit2 (4153934827/5242880000) (rectSplit2 (32851546091/41943040000) (rectLeaf (by decide +kernel)) (rectSplit1 (411/32000) (rectSplit2 (263192301253/335544320000) (rectLeaf (by decide +kernel)) (rectSplit2 (2118836048399/2684354560000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (411/4000) (rectSplit2 (138667/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (959/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell062_covered : CellCovered ⟨274,3872738,1404412⟩ ⟨275,3869757,1403292⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨274,3872738,1404412⟩ ⟨275,3869757,1403292⟩ (137/500) (11/40) 0 (11/40) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (33/320) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit2 (466601/640000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (204583/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (429/2560) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (11/80) (rectSplit2 (131009/160000) (rectSplit2 (515831/640000) (rectSplit2 (4003573/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (16383517/20480000) (rectSplit2 (130698911/163840000) (rectSplit2 (1043006713/1310720000) (rectSplit2 (8325961679/10485760000) (rectSplit2 (66481049257/83886080000) (rectSplit1 (11/640) (rectSplit2 (525642829481/671088640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4211348200423/5368709120000) (rectLeaf (by decide +kernel)) (rectSplit2 (33907980363509/42949672960000) (rectSplit2 (270612258627697/343597383680000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (33/320) (rectSplit2 (138667/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (77/320) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell063_covered : CellCovered ⟨275,3869757,1403292⟩ ⟨276,3866808,1402169⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨275,3869757,1403292⟩ ⟨276,3866808,1402169⟩ (11/40) (69/250) 0 (69/250) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (207/2000) (rectSplit2 (220993/320000) (rectLeaf (by decide +kernel)) (rectSplit2 (1891019/2560000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (204583/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (2691/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (69/500) (rectSplit2 (131009/160000) (rectSplit2 (515831/640000) (rectSplit2 (4003573/5120000) (rectLeaf (by decide +kernel)) (rectSplit2 (16383517/20480000) (rectSplit2 (130698911/163840000) (rectSplit2 (1043006713/1310720000) (rectSplit2 (8325961679/10485760000) (rectSplit1 (69/4000) (rectSplit2 (65721184207/83886080000) (rectLeaf (by decide +kernel)) (rectSplit2 (526655982881/671088640000) (rectLeaf (by decide +kernel)) (rectSplit2 (1059517530337/1342177280000) (rectLeaf (by decide +kernel)) (rectSplit1 (69/32000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (207/2000) (rectSplit2 (138667/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (483/2000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell064_covered : CellCovered ⟨276,3866808,1402169⟩ ⟨277,3863891,1401041⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨276,3866808,1402169⟩ ⟨277,3863891,1401041⟩ (69/250) (277/1000) 0 (277/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (831/8000) (rectSplit2 (220993/320000) (rectLeaf (by decide +kernel)) (rectSplit2 (1891019/2560000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (204583/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (10803/64000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (277/2000) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2071529/2560000) (rectSplit2 (8212271/10240000) (rectSplit2 (64147423/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (277/16000) (rectSplit2 (261241927/327680000) (rectSplit2 (2057369771/2621440000) (rectLeaf (by decide +kernel)) (rectSplit2 (16556655103/20971520000) (rectLeaf (by decide +kernel)) (rectSplit2 (132941725499/167772160000) (rectLeaf (by decide +kernel)) (rectSplit2 (266697592123/335544320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (831/8000) (rectSplit2 (138667/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (1939/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell065_covered : CellCovered ⟨277,3863891,1401041⟩ ⟨278,3861005,1399909⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨277,3863891,1401041⟩ ⟨278,3861005,1399909⟩ (277/1000) (139/500) 0 (139/500) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (417/4000) (rectSplit2 (220993/320000) (rectLeaf (by decide +kernel)) (rectSplit2 (1891019/2560000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (204583/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (5421/32000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (139/1000) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2071529/2560000) (rectSplit2 (8212271/10240000) (rectSplit2 (64147423/81920000) (rectLeaf (by decide +kernel)) (rectSplit1 (139/8000) (rectSplit2 (524034599/655360000) (rectSplit2 (4181421577/5242880000) (rectSplit2 (32919467081/41943040000) (rectLeaf (by decide +kernel)) (rectSplit2 (264951453253/335544320000) (rectLeaf (by decide +kernel)) (rectSplit2 (2127590209049/2684354560000) (rectLeaf (by decide +kernel)) (rectSplit2 (4268478056473/5368709120000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (417/4000) (rectSplit2 (138667/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (973/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell066_covered : CellCovered ⟨278,3861005,1399909⟩ ⟨279,3858621,1398699⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨278,3861005,1399909⟩ ⟨279,3858621,1398699⟩ (139/500) (279/1000) 0 (279/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (837/8000) (rectSplit2 (220993/320000) (rectLeaf (by decide +kernel)) (rectSplit2 (1891019/2560000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (204583/320000) (rectLeaf (by decide +kernel)) (rectSplit1 (10881/64000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (279/2000) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2071529/2560000) (rectSplit2 (16498387/20480000) (rectSplit2 (131470181/163840000) (rectSplit2 (1026432613/1310720000) (rectLeaf (by decide +kernel)) (rectSplit1 (279/16000) (rectSplit2 (8388762749/10485760000) (rectSplit2 (66932800147/83886080000) (rectSplit2 (526774610771/671088640000) (rectLeaf (by decide +kernel)) (rectSplit2 (4240260257383/5368709120000) (rectLeaf (by decide +kernel)) (rectSplit2 (34139276819189/42949672960000) (rectSplit2 (272462630273137/343597383680000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (837/8000) (rectSplit2 (138667/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (1953/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell067_covered : CellCovered ⟨279,3858621,1398699⟩ ⟨280,3855819,1397675⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨279,3858621,1398699⟩ ⟨280,3855819,1397675⟩ (279/1000) (7/25) 0 (7/25) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (7/50) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (7/100) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (77/400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (7/50) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2071529/2560000) (rectSplit2 (16498387/20480000) (rectSplit2 (131470181/163840000) (rectSplit2 (1026432613/1310720000) (rectLeaf (by decide +kernel)) (rectSplit1 (7/400) (rectSplit2 (8388762749/10485760000) (rectSplit2 (65868989077/83886080000) (rectLeaf (by decide +kernel)) (rectSplit2 (530675251361/671088640000) (rectLeaf (by decide +kernel)) (rectSplit1 (7/3200) (rectSplit2 (1067556067297/1342177280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (21/200) (rectSplit2 (138667/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (49/200) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell068_covered : CellCovered ⟨280,3855819,1397675⟩ ⟨281,3853046,1396649⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨280,3855819,1397675⟩ ⟨281,3853046,1396649⟩ (7/25) (281/1000) 0 (281/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (281/2000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (281/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (3091/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (281/2000) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2071529/2560000) (rectSplit2 (16498387/20480000) (rectSplit2 (128368691/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (281/16000) (rectSplit2 (517093169/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (2100938321/2621440000) (rectSplit1 (281/128000) (rectSplit2 (16709809633/20971520000) (rectSplit2 (33256791041/41943040000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (843/8000) (rectSplit2 (138667/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (1967/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell069_covered : CellCovered ⟨281,3853046,1396649⟩ ⟨282,3850303,1395619⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨281,3853046,1396649⟩ ⟨282,3850303,1395619⟩ (281/1000) (141/500) 0 (141/500) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (141/1000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (141/2000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (1551/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (141/1000) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2071529/2560000) (rectSplit2 (16498387/20480000) (rectSplit2 (128368691/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (141/8000) (rectSplit2 (517093169/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (2100938321/2621440000) (rectSplit2 (16644678343/20971520000) (rectLeaf (by decide +kernel)) (rectSplit2 (133971567869/167772160000) (rectSplit1 (141/64000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (423/4000) (rectSplit2 (138667/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (987/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

theorem cell070_covered : CellCovered ⟨282,3850303,1395619⟩ ⟨283,3847588,1394585⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨282,3850303,1395619⟩ ⟨283,3847588,1394585⟩ (141/500) (283/1000) 0 (283/1000) (703/1250) 1 from
    (rectSplit2 (8359/10000) (rectSplit2 (30701/40000) (rectSplit1 (283/2000) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (283/4000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectSplit2 (53197/80000) (rectLeaf (by decide +kernel)) (rectSplit1 (3113/16000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))))) (rectSplit1 (283/2000) (rectSplit2 (131009/160000) (rectSplit2 (499421/640000) (rectLeaf (by decide +kernel)) (rectSplit2 (2071529/2560000) (rectSplit2 (16498387/20480000) (rectSplit2 (128368691/163840000) (rectLeaf (by decide +kernel)) (rectSplit1 (283/16000) (rectSplit2 (517093169/655360000) (rectLeaf (by decide +kernel)) (rectSplit2 (2100938321/2621440000) (rectSplit2 (16644678343/20971520000) (rectLeaf (by decide +kernel)) (rectSplit2 (133971567869/167772160000) (rectSplit1 (283/128000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (14359/16000) (rectSplit1 (849/8000) (rectSplit2 (138667/160000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (1981/8000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 60).take 11), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨272,3878795,1406641⟩,⟨273,3875751,1405529⟩),(⟨273,3875751,1405529⟩,⟨274,3872738,1404412⟩),(⟨274,3872738,1404412⟩,⟨275,3869757,1403292⟩),(⟨275,3869757,1403292⟩,⟨276,3866808,1402169⟩),(⟨276,3866808,1402169⟩,⟨277,3863891,1401041⟩),(⟨277,3863891,1401041⟩,⟨278,3861005,1399909⟩),(⟨278,3861005,1399909⟩,⟨279,3858621,1398699⟩),(⟨279,3858621,1398699⟩,⟨280,3855819,1397675⟩),(⟨280,3855819,1397675⟩,⟨281,3853046,1396649⟩),(⟨281,3853046,1396649⟩,⟨282,3850303,1395619⟩),(⟨282,3850303,1395619⟩,⟨283,3847588,1394585⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell060_covered ?_
  refine slabCons cell061_covered ?_
  refine slabCons cell062_covered ?_
  refine slabCons cell063_covered ?_
  refine slabCons cell064_covered ?_
  refine slabCons cell065_covered ?_
  refine slabCons cell066_covered ?_
  refine slabCons cell067_covered ?_
  refine slabCons cell068_covered ?_
  refine slabCons cell069_covered ?_
  refine slabCons cell070_covered ?_
  simp
