-- Prove2me | solution 1 for ThreeSum.WeightedSourceCountExecutionFactory.Seed.finish
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:41:31.84427+00:00
-- url     : https://prove2.me/submissions/0fb2f660-52f7-49bb-92ab-c9c34928e6fb

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_SourceCountExecutionFactory
import Definitions.Def_Submission_ThreeSum_TernarySourceWeightSeed
import Definitions.Def_Submission_Weighted_Global_TernarySourceCountWeightSeed
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_transport
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_layout
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_transport
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_transport
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_transport


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedSourceCountExecutionFactory
open Light TernaryJointType
namespace ThreeSum.WeightedSourceCountExecutionFactory
namespace Seed
theorem _root_.solution {N : ℕ} {S : Setup N} {lim : Limits} {d boundary : ℕ}
    {μ ν : ℕ→ℤ} {leftWeight rightWeight : ℕ→ℤ}
    (H : Seed S lim d boundary μ leftWeight rightWeight) (hkeep : Kept μ ν boundary)
    (hleftRead : ∀ i<S.left.NL, ν (S.left.weightBase+i)=leftWeight i)
    (hrightRead : ∀ i<S.right.NL, ν (S.right.weightBase+i)=rightWeight i) :
    Ready S lim d ν leftWeight rightWeight where
  layout := H.layout
  left := (H.left.transport hkeep H.leftInputBefore H.leftCodesBefore H.leftPowersBefore).finish hleftRead
  right := (H.right.transport hkeep H.rightInputBefore H.rightCodesBefore H.rightPowersBefore).finish hrightRead
  front := H.front.transport hkeep H.frontCodesBefore H.frontRecordsBefore
  depth := H.depth
end Seed
end ThreeSum.WeightedSourceCountExecutionFactory
