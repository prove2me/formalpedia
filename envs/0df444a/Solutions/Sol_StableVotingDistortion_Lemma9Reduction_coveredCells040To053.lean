-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.coveredCells040To053
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:37:23.465349+00:00
-- url     : https://prove2.me/submissions/b1abc9f2-16ee-4dc9-9a40-8357a2cb1df3

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
theorem cell040_covered : CellCovered ⟨252,3946093,1428205⟩ ⟨253,3942192,1427204⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨252,3946093,1428205⟩ ⟨253,3942192,1427204⟩ (63/250) (253/1000) 0 (253/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (1771/8000) (rectSplit1 (12397/64000) (rectSplit1 (37191/256000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (111573/2048000) (rectSplit2 (941407/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (759/8000) (rectSplit2 (253813/320000) (rectSplit2 (1000483/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (4016701/5120000) (rectSplit2 (8018633/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (759/64000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (137573/160000) (rectSplit2 (1075969/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell041_covered : CellCovered ⟨253,3942192,1427204⟩ ⟨254,3938339,1426196⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨253,3942192,1427204⟩ ⟨254,3938339,1426196⟩ (253/1000) (127/500) 0 (127/500) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (889/4000) (rectSplit1 (6223/32000) (rectSplit1 (18669/128000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (56007/1024000) (rectSplit2 (941407/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (381/4000) (rectSplit2 (253813/320000) (rectSplit2 (1000483/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (4016701/5120000) (rectSplit2 (8018633/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (381/32000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (137573/160000) (rectSplit2 (266941/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell042_covered : CellCovered ⟨254,3938339,1426196⟩ ⟨255,3934536,1425182⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨254,3938339,1426196⟩ ⟨255,3934536,1425182⟩ (127/500) (51/200) 0 (51/200) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (357/1600) (rectSplit1 (2499/12800) (rectSplit1 (7497/51200) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (22491/409600) (rectSplit2 (941407/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (153/1600) (rectSplit2 (253813/320000) (rectSplit2 (1000483/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (4016701/5120000) (rectSplit2 (8018633/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (153/12800) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit2 (137573/160000) (rectSplit2 (266941/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell043_covered : CellCovered ⟨255,3934536,1425182⟩ ⟨256,3930782,1424162⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨255,3934536,1425182⟩ ⟨256,3930782,1424162⟩ (51/200) (32/125) 0 (32/125) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (28/125) (rectSplit1 (49/250) (rectSplit1 (147/1000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (441/8000) (rectSplit2 (941407/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (12/125) (rectSplit2 (253813/320000) (rectSplit2 (1000483/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (4016701/5120000) (rectSplit2 (8018633/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (3/250) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (4/25) (rectSplit2 (137573/160000) (rectSplit2 (266941/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell044_covered : CellCovered ⟨256,3930782,1424162⟩ ⟨257,3927076,1423136⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨256,3930782,1424162⟩ ⟨257,3927076,1423136⟩ (32/125) (257/1000) 0 (257/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (1799/8000) (rectSplit1 (12593/64000) (rectSplit1 (37779/256000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (113337/2048000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (771/8000) (rectSplit2 (253813/320000) (rectSplit2 (1000483/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (4016701/5120000) (rectSplit2 (8018633/10240000) (rectLeaf (by decide +kernel)) (rectSplit1 (771/64000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (257/1600) (rectSplit2 (137573/160000) (rectSplit2 (266941/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell045_covered : CellCovered ⟨257,3927076,1423136⟩ ⟨258,3923418,1422103⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨257,3927076,1423136⟩ ⟨258,3923418,1422103⟩ (257/1000) (129/500) 0 (129/500) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (903/4000) (rectSplit1 (6321/32000) (rectSplit1 (18963/128000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (56889/1024000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (387/4000) (rectSplit2 (253813/320000) (rectSplit2 (1000483/1280000) (rectLeaf (by decide +kernel)) (rectSplit2 (8048171/10240000) (rectSplit2 (3210407/4096000) (rectSplit1 (387/32000) (rectSplit2 (64163833/81920000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectSplit1 (129/800) (rectSplit2 (137573/160000) (rectSplit2 (266941/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell046_covered : CellCovered ⟨258,3923418,1422103⟩ ⟨259,3919808,1421064⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨258,3923418,1422103⟩ ⟨259,3919808,1421064⟩ (129/500) (259/1000) 0 (259/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (1813/8000) (rectSplit1 (12691/64000) (rectSplit1 (38073/256000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (114219/2048000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (777/8000) (rectSplit2 (24889/32000) (rectLeaf (by decide +kernel)) (rectSplit2 (40807/51200) (rectSplit2 (1617511/2048000) (rectSplit2 (12866243/16384000) (rectSplit2 (102806869/131072000) (rectSplit2 (410365951/524288000) (rectLeaf (by decide +kernel)) (rectSplit2 (3287235233/4194304000) (rectSplit1 (777/64000) (rectSplit2 (13144633307/16777216000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (259/1600) (rectSplit2 (137573/160000) (rectSplit2 (266941/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell047_covered : CellCovered ⟨259,3919808,1421064⟩ ⟨260,3916246,1420019⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨259,3919808,1421064⟩ ⟨260,3916246,1420019⟩ (259/1000) (13/50) 0 (13/50) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (91/400) (rectSplit1 (637/3200) (rectSplit1 (1911/12800) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (5733/102400) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (39/400) (rectSplit2 (24889/32000) (rectLeaf (by decide +kernel)) (rectSplit2 (40807/51200) (rectSplit2 (1617511/2048000) (rectSplit2 (12866243/16384000) (rectSplit2 (102806869/131072000) (rectSplit2 (821593427/1048576000) (rectSplit1 (39/3200) (rectSplit2 (6566716741/8388608000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (13/80) (rectSplit2 (137573/160000) (rectSplit2 (266941/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell048_covered : CellCovered ⟨260,3916246,1420019⟩ ⟨261,3913874,1418739⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨260,3916246,1420019⟩ ⟨261,3913874,1418739⟩ (13/50) (261/1000) 0 (261/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (1827/8000) (rectSplit1 (12789/64000) (rectSplit1 (38367/256000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (115101/2048000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (783/8000) (rectSplit2 (24889/32000) (rectLeaf (by decide +kernel)) (rectSplit2 (40807/51200) (rectSplit2 (1617511/2048000) (rectSplit2 (12866243/16384000) (rectSplit2 (51341897/65536000) (rectLeaf (by decide +kernel)) (rectSplit2 (410858251/524288000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (261/1600) (rectSplit2 (137573/160000) (rectSplit2 (266941/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell049_covered : CellCovered ⟨261,3913874,1418739⟩ ⟨262,3910422,1417677⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨261,3913874,1418739⟩ ⟨262,3910422,1417677⟩ (261/1000) (131/500) 0 (131/500) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (917/4000) (rectSplit1 (6419/32000) (rectSplit1 (19257/128000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (57771/1024000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (393/4000) (rectSplit2 (24889/32000) (rectLeaf (by decide +kernel)) (rectSplit2 (40807/51200) (rectSplit2 (1617511/2048000) (rectSplit2 (6445429/8192000) (rectSplit2 (12817013/16384000) (rectLeaf (by decide +kernel)) (rectSplit1 (393/32000) (rectSplit2 (102757639/131072000) (rectSplit2 (821396507/1048576000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (131/800) (rectSplit2 (137573/160000) (rectSplit2 (266941/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell050_covered : CellCovered ⟨262,3910422,1417677⟩ ⟨263,3907016,1416610⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨262,3910422,1417677⟩ ⟨263,3907016,1416610⟩ (131/500) (263/1000) 0 (263/1000) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (1841/8000) (rectSplit1 (12887/64000) (rectSplit1 (38661/256000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (115983/2048000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (789/8000) (rectSplit2 (24889/32000) (rectLeaf (by decide +kernel)) (rectSplit2 (40807/51200) (rectSplit2 (1617511/2048000) (rectSplit2 (6445429/8192000) (rectSplit2 (12817013/16384000) (rectLeaf (by decide +kernel)) (rectSplit1 (789/64000) (rectSplit2 (102757639/131072000) (rectSplit2 (821396507/1048576000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (263/1600) (rectSplit2 (137573/160000) (rectSplit2 (266941/320000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell051_covered : CellCovered ⟨263,3907016,1416610⟩ ⟨264,3903654,1415537⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨263,3907016,1416610⟩ ⟨264,3903654,1415537⟩ (263/1000) (33/125) 0 (33/125) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (231/1000) (rectSplit1 (1617/8000) (rectSplit1 (4851/32000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (14553/256000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (99/1000) (rectSplit2 (24889/32000) (rectLeaf (by decide +kernel)) (rectSplit2 (40807/51200) (rectSplit2 (1617511/2048000) (rectSplit2 (6445429/8192000) (rectSplit2 (12817013/16384000) (rectLeaf (by decide +kernel)) (rectSplit1 (99/8000) (rectSplit2 (102757639/131072000) (rectSplit2 (821396507/1048576000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (33/200) (rectSplit2 (137573/160000) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell052_covered : CellCovered ⟨264,3903654,1415537⟩ ⟨265,3900327,1414459⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨264,3903654,1415537⟩ ⟨265,3900327,1414459⟩ (33/125) (53/200) 0 (53/200) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (371/1600) (rectSplit1 (2597/12800) (rectSplit1 (7791/51200) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (23373/409600) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (159/1600) (rectSplit2 (24889/32000) (rectLeaf (by decide +kernel)) (rectSplit2 (40807/51200) (rectSplit2 (801371/1024000) (rectLeaf (by decide +kernel)) (rectSplit2 (6484813/8192000) (rectSplit2 (12895781/16384000) (rectSplit2 (102649333/131072000) (rectLeaf (by decide +kernel)) (rectSplit1 (159/12800) (rectSplit2 (411114247/524288000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (53/320) (rectSplit2 (137573/160000) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

theorem cell053_covered : CellCovered ⟨265,3900327,1414459⟩ ⟨266,3897034,1413378⟩ := by
  apply StableVotingDistortion.Lemma9Reduction.rectWitnessSound (by decide +kernel) (by decide +kernel)
  convert (show RectWitness ⟨265,3900327,1414459⟩ ⟨266,3897034,1413378⟩ (53/200) (133/500) 0 (133/500) (703/1250) 1 from
    (rectSplit2 (4453/5000) (rectSplit2 (16171/20000) (rectSplit2 (59761/80000) (rectSplit1 (931/4000) (rectSplit1 (6517/32000) (rectSplit1 (19551/128000) (rectSplit2 (104753/160000) (rectLeaf (by decide +kernel)) (rectSplit1 (58653/1024000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectSplit1 (399/4000) (rectSplit2 (24889/32000) (rectLeaf (by decide +kernel)) (rectSplit2 (40807/51200) (rectSplit2 (801371/1024000) (rectLeaf (by decide +kernel)) (rectSplit2 (6484813/8192000) (rectSplit2 (51656969/65536000) (rectSplit2 (206258651/262144000) (rectSplit2 (1642315483/2097152000) (rectLeaf (by decide +kernel)) (rectSplit1 (399/32000) (rectSplit2 (13146277589/16777216000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) (rectSplit1 (133/800) (rectSplit2 (137573/160000) (rectSplit2 (1059559/1280000) (rectLeaf (by decide +kernel)) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel))) (rectLeaf (by decide +kernel)))) (rectLeaf (by decide +kernel)))) using 1 <;> decide +kernel

end StableVotingDistortion.PaperMiddle
open StableVotingDistortion StableVotingDistortion.PaperMiddle

private theorem slabCons {x : Knot × Knot} {xs : List (Knot × Knot)}
    (hx : CellCovered x.1 x.2) (ht : ∀ cd ∈ xs, CellCovered cd.1 cd.2) :
    ∀ cd ∈ x :: xs, CellCovered cd.1 cd.2 := List.forall_mem_cons.mpr ⟨hx, ht⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ ((adjacentCells.drop 40).take 14), CellCovered cd.1 cd.2 := by
  change ∀ cd ∈ ([(⟨252,3946093,1428205⟩,⟨253,3942192,1427204⟩),(⟨253,3942192,1427204⟩,⟨254,3938339,1426196⟩),(⟨254,3938339,1426196⟩,⟨255,3934536,1425182⟩),(⟨255,3934536,1425182⟩,⟨256,3930782,1424162⟩),(⟨256,3930782,1424162⟩,⟨257,3927076,1423136⟩),(⟨257,3927076,1423136⟩,⟨258,3923418,1422103⟩),(⟨258,3923418,1422103⟩,⟨259,3919808,1421064⟩),(⟨259,3919808,1421064⟩,⟨260,3916246,1420019⟩),(⟨260,3916246,1420019⟩,⟨261,3913874,1418739⟩),(⟨261,3913874,1418739⟩,⟨262,3910422,1417677⟩),(⟨262,3910422,1417677⟩,⟨263,3907016,1416610⟩),(⟨263,3907016,1416610⟩,⟨264,3903654,1415537⟩),(⟨264,3903654,1415537⟩,⟨265,3900327,1414459⟩),(⟨265,3900327,1414459⟩,⟨266,3897034,1413378⟩)] : List (Knot × Knot)), CellCovered cd.1 cd.2
  refine slabCons cell040_covered ?_
  refine slabCons cell041_covered ?_
  refine slabCons cell042_covered ?_
  refine slabCons cell043_covered ?_
  refine slabCons cell044_covered ?_
  refine slabCons cell045_covered ?_
  refine slabCons cell046_covered ?_
  refine slabCons cell047_covered ?_
  refine slabCons cell048_covered ?_
  refine slabCons cell049_covered ?_
  refine slabCons cell050_covered ?_
  refine slabCons cell051_covered ?_
  refine slabCons cell052_covered ?_
  refine slabCons cell053_covered ?_
  simp
