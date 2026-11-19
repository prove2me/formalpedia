-- Prove2me | solution 1 for QEC.Distillation.BK15.l1Words_disjoint_l1LogicalCosetWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:09:03.966137+00:00
-- url     : https://prove2.me/submissions/f90ff2e8-0397-42a6-a49f-661593b0e2c1

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l1CoefficientMap_mem
import Theorems.Thm_QEC_Distillation_BK15_allOnes_not_mem_L1

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : Disjoint l1Words l1LogicalCosetWords := by
  apply Finset.disjoint_left.mpr
  intro w hw hcoset
  rw [l1Words, Finset.mem_image] at hw
  rcases hw with ⟨a, _, ha⟩
  rw [l1LogicalCosetWords, Finset.mem_image] at hcoset
  rcases hcoset with ⟨u, hu, hu_eq⟩
  rw [l1Words, Finset.mem_image] at hu
  rcases hu with ⟨b, _, hb⟩
  apply allOnes_not_mem_L1
  have hdiff : l1CoefficientMap a - l1CoefficientMap b = allOnes := by
    rw [ha, hb, ← hu_eq]
    abel
  rw [← hdiff]
  exact L1.carrier.sub_mem (l1CoefficientMap_mem a) (l1CoefficientMap_mem b)
end QEC.Distillation.BK15
