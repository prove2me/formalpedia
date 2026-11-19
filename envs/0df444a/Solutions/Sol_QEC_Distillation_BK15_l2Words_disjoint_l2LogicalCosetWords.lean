-- Prove2me | solution 1 for QEC.Distillation.BK15.l2Words_disjoint_l2LogicalCosetWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:08:38.925097+00:00
-- url     : https://prove2.me/submissions/78d1f1c5-d8ce-4dce-a255-134ca9345421

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2CoefficientMap_mem
import Theorems.Thm_QEC_Distillation_BK15_allOnes_not_mem_L2

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : Disjoint l2Words l2LogicalCosetWords := by
  apply Finset.disjoint_left.mpr
  intro w hw hcoset
  rw [l2Words, Finset.mem_image] at hw
  rcases hw with ⟨a, _, ha⟩
  rw [l2LogicalCosetWords, Finset.mem_image] at hcoset
  rcases hcoset with ⟨u, hu, hu_eq⟩
  rw [l2Words, Finset.mem_image] at hu
  rcases hu with ⟨b, _, hb⟩
  apply allOnes_not_mem_L2
  have hdiff : l2CoefficientMap a - l2CoefficientMap b = allOnes := by
    rw [ha, hb, ← hu_eq]
    abel
  rw [← hdiff]
  exact L2.carrier.sub_mem (l2CoefficientMap_mem a) (l2CoefficientMap_mem b)
end QEC.Distillation.BK15
